# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# Copyright 2014 SoftLayer Technologies, Inc.
# Copyright 2015 Mirantis, Inc
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""
System-level utilities and helper functions.
"""

import base64
import collections.abc
import contextlib
import errno
import functools
import grp
import hashlib
import itertools
import os
import pwd
import re
import urllib.parse
import uuid

from time import sleep

from cryptography import x509
from oslo_config import cfg
from oslo_log import log as logging
from oslo_serialization import jsonutils
from oslo_utils import excutils, netutils, reflection, strutils, timeutils
from webob import exc

from everest.common import exception
from everest.common import password_hashing
from everest.i18n import _

CONF = cfg.CONF
LOG = logging.getLogger(__name__)


WHITELISTED_PROPERTIES = [
    'tenant_id', 'project_id', 'user_id',
    'public_bind_host', 'admin_bind_host',
    'compute_host', 'admin_port', 'public_port',
    'public_endpoint', ]


# NOTE(stevermar): This UUID must stay the same, forever, across
# all of keystone to preserve its value as a URN namespace, which is
# used for ID transformation.
RESOURCE_ID_NAMESPACE = uuid.UUID('4332ecab-770b-4288-a680-b9aca3b1b153')

# Compatibilty for password hashing functions.
verify_length_and_trunc_password = password_hashing.verify_length_and_trunc_password  # noqa
hash_password = password_hashing.hash_password
hash_user_password = password_hashing.hash_user_password
check_password = password_hashing.check_password


# NOTE(hiromu): This dict defines alternative DN string for X.509. When
# retriving DN from X.509, converting attributes types that are not listed
# in the RFC4514 to a corresponding alternative DN string.
ATTR_NAME_OVERRIDES = {
    x509.NameOID.EMAIL_ADDRESS: "emailAddress",
}


def resource_uuid(value):
    """Convert input to valid UUID hex digits."""
    try:
        uuid.UUID(value)
        return value
    except ValueError:
        if len(value) <= 64:
            return uuid.uuid5(RESOURCE_ID_NAMESPACE, value).hex
        raise ValueError(_('Length of transformable resource id > 64, '
                         'which is max allowed characters'))


def flatten_dict(d, parent_key=''):
    """Flatten a nested dictionary.

    Converts a dictionary with nested values to a single level flat
    dictionary, with dotted notation for each key.

    """
    items = []
    for k, v in d.items():
        new_key = parent_key + '.' + k if parent_key else k
        if isinstance(v, collections.abc.MutableMapping):
            items.extend(list(flatten_dict(v, new_key).items()))
        else:
            items.append((new_key, v))
    return dict(items)


class SmarterEncoder(jsonutils.json.JSONEncoder):
    """Help for JSON encoding dict-like objects."""

    def default(self, obj):
        if not isinstance(obj, dict) and hasattr(obj, 'items'):
            return dict(obj.items())
        return super(SmarterEncoder, self).default(obj)


def hash_access_key(access):
    hash_ = hashlib.sha256()
    if not isinstance(access, bytes):
        access = access.encode('utf-8')
    hash_.update(access)
    return hash_.hexdigest()


def attr_as_boolean(val_attr):
    """Return the boolean value, decoded from a string.

    We test explicitly for a value meaning False, which can be one of
    several formats as specified in oslo strutils.FALSE_STRINGS.
    All other string values (including an empty string) are treated as
    meaning True.

    """
    return strutils.bool_from_string(val_attr, default=True)


def auth_str_equal(provided, known):
    """Constant-time string comparison.

    :params provided: the first string
    :params known: the second string

    :returns: True if the strings are equal.

    This function takes two strings and compares them.  It is intended to be
    used when doing a comparison for authentication purposes to help guard
    against timing attacks.  When using the function for this purpose, always
    provide the user-provided password as the first argument.  The time this
    function will take is always a factor of the length of this string.
    """
    result = 0
    p_len = len(provided)
    k_len = len(known)
    for i in range(p_len):
        a = ord(provided[i]) if i < p_len else 0
        b = ord(known[i]) if i < k_len else 0
        result |= a ^ b
    return (p_len == k_len) & (result == 0)


def setup_remote_pydev_debug():
    if CONF.pydev_debug_host and CONF.pydev_debug_port:
        try:
            try:
                from pydev import pydevd
            except ImportError:
                import pydevd

            pydevd.settrace(CONF.pydev_debug_host,
                            port=CONF.pydev_debug_port,
                            stdoutToServer=True,
                            stderrToServer=True)
            return True
        except Exception:
            LOG.exception(
                'Error setting up the debug environment. Verify that the '
                'option --debug-url has the format <host>:<port> and that a '
                'debugger processes is listening on that port.')
            raise


def get_unix_user(user=None):
    """Get the uid and user name.

    This is a convenience utility which accepts a variety of input
    which might represent a unix user. If successful it returns the uid
    and name. Valid input is:

    string
        A string is first considered to be a user name and a lookup is
        attempted under that name. If no name is found then an attempt
        is made to convert the string to an integer and perform a
        lookup as a uid.

    int
        An integer is interpreted as a uid.

    None
        None is interpreted to mean use the current process's
        effective user.

    If the input is a valid type but no user is found a KeyError is
    raised. If the input is not a valid type a TypeError is raised.

    :param object user: string, int or None specifying the user to
                        lookup.

    :returns: tuple of (uid, name)

    """
    if isinstance(user, str):
        try:
            user_info = pwd.getpwnam(user)
        except KeyError:
            try:
                i = int(user)
            except ValueError:
                raise KeyError("user name '%s' not found" % user)
            try:
                user_info = pwd.getpwuid(i)
            except KeyError:
                raise KeyError("user id %d not found" % i)
    elif isinstance(user, int):
        try:
            user_info = pwd.getpwuid(user)
        except KeyError:
            raise KeyError("user id %d not found" % user)
    elif user is None:
        user_info = pwd.getpwuid(os.geteuid())
    else:
        user_cls_name = reflection.get_class_name(user,
                                                  fully_qualified=False)
        raise TypeError('user must be string, int or None; not %s (%r)' %
                        (user_cls_name, user))

    return user_info.pw_uid, user_info.pw_name


def get_unix_group(group=None):
    """Get the gid and group name.

    This is a convenience utility which accepts a variety of input
    which might represent a unix group. If successful it returns the gid
    and name. Valid input is:

    string
        A string is first considered to be a group name and a lookup is
        attempted under that name. If no name is found then an attempt
        is made to convert the string to an integer and perform a
        lookup as a gid.

    int
        An integer is interpreted as a gid.

    None
        None is interpreted to mean use the current process's
        effective group.

    If the input is a valid type but no group is found a KeyError is
    raised. If the input is not a valid type a TypeError is raised.


    :param object group: string, int or None specifying the group to
                         lookup.

    :returns: tuple of (gid, name)

    """
    if isinstance(group, str):
        try:
            group_info = grp.getgrnam(group)
        except KeyError:
            # Was an int passed as a string?
            # Try converting to int and lookup by id instead.
            try:
                i = int(group)
            except ValueError:
                raise KeyError("group name '%s' not found" % group)
            try:
                group_info = grp.getgrgid(i)
            except KeyError:
                raise KeyError("group id %d not found" % i)
    elif isinstance(group, int):
        try:
            group_info = grp.getgrgid(group)
        except KeyError:
            raise KeyError("group id %d not found" % group)
    elif group is None:
        group_info = grp.getgrgid(os.getegid())
    else:
        group_cls_name = reflection.get_class_name(group,
                                                   fully_qualified=False)
        raise TypeError('group must be string, int or None; not %s (%r)' %
                        (group_cls_name, group))

    return group_info.gr_gid, group_info.gr_name


class WhiteListedItemFilter(object):

    def __init__(self, whitelist, data):
        self._whitelist = set(whitelist or [])
        self._data = data

    def __getitem__(self, name):
        """Evaluation on an item access."""
        if name not in self._whitelist:
            raise KeyError
        return self._data[name]


_ISO8601_TIME_FORMAT_SUBSECOND = '%Y-%m-%dT%H:%M:%S.%f'
_ISO8601_TIME_FORMAT = '%Y-%m-%dT%H:%M:%S'


def isotime(at=None, subsecond=False):
    """Stringify time in ISO 8601 format.

    Python provides a similar instance method for datetime.datetime objects
    called `isoformat()`. The format of the strings generated by `isoformat()`
    has a couple of problems:

    1) The strings generated by `isotime()` are used in tokens and other public
    APIs that we can't change without a deprecation period. The strings
    generated by `isoformat()` are not the same format, so we can't just
    change to it.

    2) The strings generated by `isoformat()` do not include the microseconds
    if the value happens to be 0. This will likely show up as random
    failures as parsers may be written to always expect microseconds, and it
    will parse correctly most of the time.

    :param at: Optional datetime object to return at a string. If not provided,
               the time when the function was called will be used.
    :type at: datetime.datetime
    :param subsecond: If true, the returned string will represent microsecond
                      precision, but only precise to the second. For example, a
                      `datetime.datetime(2016, 9, 14, 14, 1, 13, 970223)` will
                      be returned as `2016-09-14T14:01:13.000000Z`.
    :type subsecond: bool
    :returns: A time string represented in ISO 8601 format.
    :rtype: str
    """
    if not at:
        at = timeutils.utcnow()
    # NOTE(lbragstad): Datetime objects are immutable, so reassign the date we
    # are working with to itself as we drop microsecond precision.
    at = at.replace(microsecond=0)
    st = at.strftime(_ISO8601_TIME_FORMAT
                     if not subsecond
                     else _ISO8601_TIME_FORMAT_SUBSECOND)
    tz = at.tzinfo.tzname(None) if at.tzinfo else 'UTC'
    # Need to handle either iso8601 or python UTC format
    st += ('Z' if tz in ['UTC', 'UTC+00:00'] else tz)
    return st


def parse_expiration_date(expiration_date):
    if not expiration_date.endswith('Z'):
        expiration_date += 'Z'
    try:
        expiration_time = timeutils.parse_isotime(expiration_date)
    except ValueError:
        raise exception.ValidationTimeStampError()
    if timeutils.is_older_than(expiration_time, 0):
        raise exception.ValidationExpirationError()
    return expiration_time


URL_RESERVED_CHARS = ":/?#[]@!$&'()*+,;="


def is_not_url_safe(name):
    """Check if a string contains any url reserved characters."""
    return len(list_url_unsafe_chars(name)) > 0


def list_url_unsafe_chars(name):
    """Return a list of the reserved characters."""
    reserved_chars = ''
    for i in name:
        if i in URL_RESERVED_CHARS:
            reserved_chars += i
    return reserved_chars


def lower_case_hostname(url):
    """Change the URL's hostname to lowercase."""
    # NOTE(gyee): according to
    # https://www.w3.org/TR/WD-html40-970708/htmlweb.html, the netloc portion
    # of the URL is case-insensitive
    parsed = urllib.parse.urlparse(url)
    # Note: _replace method for named tuples is public and defined in docs
    replaced = parsed._replace(netloc=parsed.netloc.lower())
    return urllib.parse.urlunparse(replaced)


def remove_standard_port(url):
    # remove the default ports specified in RFC2616 and 2818
    o = urllib.parse.urlparse(url)
    separator = ':'
    (host, separator, port) = o.netloc.partition(separator)
    if o.scheme.lower() == 'http' and port == '80':
        # NOTE(gyee): _replace() is not a private method. It has
        # an underscore prefix to prevent conflict with field names.
        # See https://docs.python.org/2/library/collections.html#
        # collections.namedtuple
        o = o._replace(netloc=host)
    if o.scheme.lower() == 'https' and port == '443':
        o = o._replace(netloc=host)

    return urllib.parse.urlunparse(o)


def format_url(url, substitutions, silent_keyerror_failures=None):
    """Format a user-defined URL with the given substitutions.

    :param string url: the URL to be formatted
    :param dict substitutions: the dictionary used for substitution
    :param list silent_keyerror_failures: keys for which we should be silent
        if there is a KeyError exception on substitution attempt
    :returns: a formatted URL

    """
    substitutions = WhiteListedItemFilter(
        WHITELISTED_PROPERTIES,
        substitutions)
    allow_keyerror = silent_keyerror_failures or []
    try:
        result = url.replace('$(', '%(') % substitutions
    except AttributeError:
        msg = "Malformed endpoint - %(url)r is not a string"
        LOG.error(msg, {"url": url})
        raise exception.MalformedEndpoint(endpoint=url)
    except KeyError as e:
        if not e.args or e.args[0] not in allow_keyerror:
            msg = "Malformed endpoint %(url)s - unknown key %(keyerror)s"
            LOG.error(msg, {"url": url, "keyerror": e})
            raise exception.MalformedEndpoint(endpoint=url)
        else:
            result = None
    except TypeError as e:
        msg = ("Malformed endpoint '%(url)s'. The following type error "
               "occurred during string substitution: %(typeerror)s")
        LOG.error(msg, {"url": url, "typeerror": e})
        raise exception.MalformedEndpoint(endpoint=url)
    except ValueError:
        msg = ("Malformed endpoint %s - incomplete format "
               "(are you missing a type notifier ?)")
        LOG.error(msg, url)
        raise exception.MalformedEndpoint(endpoint=url)
    return result


def check_endpoint_url(url):
    """Check substitution of url.

    The invalid urls are as follows:
    urls with substitutions that is not in the whitelist

    Check the substitutions in the URL to make sure they are valid
    and on the whitelist.

    :param str url: the URL to validate
    :rtype: None
    :raises keystone.exception.URLValidationError: if the URL is invalid
    """
    # check whether the property in the path is exactly the same
    # with that in the whitelist below
    substitutions = dict(zip(WHITELISTED_PROPERTIES, itertools.repeat('')))
    try:
        url.replace('$(', '%(') % substitutions
    except (KeyError, TypeError, ValueError):
        raise exception.URLValidationError(url=url)


def get_certificate_subject_dn(cert_pem):
    """Get subject DN from the PEM certificate content.

    :param str cert_pem: the PEM certificate content
    :rtype: JSON data for subject DN
    :raises keystone.exception.ValidationError: if the PEM certificate content
        is invalid
    """
    dn_dict = {}
    try:
        cert = x509.load_pem_x509_certificate(cert_pem.encode('utf-8'))
        for item in cert.subject:
            name, value = item.rfc4514_string(
                attr_name_overrides=ATTR_NAME_OVERRIDES).split('=')
            dn_dict[name] = value
    except Exception as error:
        LOG.exception(error)
        message = _('The certificate content is not PEM format.')
        raise exception.ValidationError(message=message)
    return dn_dict


def get_certificate_issuer_dn(cert_pem):
    """Get issuer DN from the PEM certificate content.

    :param str cert_pem: the PEM certificate content
    :rtype: JSON data for issuer DN
    :raises keystone.exception.ValidationError: if the PEM certificate content
        is invalid
    """
    dn_dict = {}
    try:
        cert = x509.load_pem_x509_certificate(cert_pem.encode('utf-8'))
        for item in cert.issuer:
            name, value = item.rfc4514_string(
                attr_name_overrides=ATTR_NAME_OVERRIDES).split('=')
            dn_dict[name] = value
    except Exception as error:
        LOG.exception(error)
        message = _('The certificate content is not PEM format.')
        raise exception.ValidationError(message=message)
    return dn_dict


def get_certificate_thumbprint(cert_pem):
    """Get certificate thumbprint from the PEM certificate content.

    :param str cert_pem: the PEM certificate content
    :rtype: certificate thumbprint
    """
    thumb_sha256 = hashlib.sha256(cert_pem.encode('ascii')).digest()
    thumbprint = base64.urlsafe_b64encode(thumb_sha256).decode('ascii')
    return thumbprint


def create_directory(directory, keystone_user_id=None, keystone_group_id=None):
    """Attempt to create a directory if it doesn't exist.

    :param directory: string containing the path of the directory to create.
    :param keystone_user_id: the system ID of the process running keystone.
    :param keystone_group_id: the system ID of the group running keystone.

    """
    if not os.access(directory, os.F_OK):
        LOG.info(
            '%s does not appear to exist; attempting to create it', directory
        )

        try:
            os.makedirs(directory, 0o700)
        except OSError:
            LOG.error(
                'Failed to create %s: either it already '
                'exists or you don\'t have sufficient permissions to '
                'create it', directory
            )

        if keystone_user_id and keystone_group_id:
            os.chown(
                directory,
                keystone_user_id,
                keystone_group_id)
        elif keystone_user_id or keystone_group_id:
            LOG.warning(
                'Unable to change the ownership of key repository without '
                'a keystone user ID and keystone group ID both being '
                'provided: %s', directory)


@contextlib.contextmanager
def nested_contexts(*contexts):
    with contextlib.ExitStack() as stack:
        yield [stack.enter_context(c) for c in contexts]



def chunkreadable(iter, chunk_size=65536):
    """
    Wrap a readable iterator with a reader yielding chunks of
    a preferred size, otherwise leave iterator unchanged.

    :param iter: an iter which may also be readable
    :param chunk_size: maximum size of chunk
    """
    return chunkiter(iter, chunk_size) if hasattr(iter, 'read') else iter


def chunkiter(fp, chunk_size=65536):
    """
    Return an iterator to a file-like obj which yields fixed size chunks

    :param fp: a file-like object
    :param chunk_size: maximum size of chunk
    """
    while True:
        chunk = fp.read(chunk_size)
        if chunk:
            yield chunk
        else:
            break


def cooperative_iter(iter):
    """
    Return an iterator which schedules after each
    iteration. This can prevent eventlet thread starvation.

    :param iter: an iterator to wrap
    """
    try:
        for chunk in iter:
            sleep(0)
            yield chunk
    except Exception as err:
        with excutils.save_and_reraise_exception():
            msg = "Error: cooperative_iter exception %s" % err
            LOG.error(msg)


def cooperative_read(fd):
    """
    Wrap a file descriptor's read with a partial function which schedules
    after each read. This can prevent eventlet thread starvation.

    :param fd: a file descriptor to wrap
    """

    def readfn(*args):
        result = fd.read(*args)
        sleep(0)
        return result

    return readfn


MAX_COOP_READER_BUFFER_SIZE = 134217728  # 128M seems like a sane buffer limit


def safe_mkdirs(path):
    try:
        os.makedirs(path)
    except OSError as e:
        if e.errno != errno.EEXIST:
            raise


def mutating(func):
    """Decorator to enforce read-only logic"""

    @functools.wraps(func)
    def wrapped(self, req, *args, **kwargs):
        if req.context.read_only:
            msg = "Read-only access"
            LOG.debug(msg)
            raise exc.HTTPForbidden(msg, request=req,
                                    content_type="text/plain")
        return func(self, req, *args, **kwargs)

    return wrapped


def setup_remote_pydev_debug(host, port):
    error_msg = ('Error setting up the debug environment. Verify that the'
                 ' option pydev_worker_debug_host is pointing to a valid '
                 'hostname or IP on which a pydev server is listening on'
                 ' the port indicated by pydev_worker_debug_port.')

    try:
        try:
            from pydev import pydevd
        except ImportError:
            import pydevd

        pydevd.settrace(host,
                        port=port,
                        stdoutToServer=True,
                        stderrToServer=True)
        return True
    except Exception:
        with excutils.save_and_reraise_exception():
            LOG.exception(error_msg)


def is_valid_hostname(hostname):
    """Verify whether a hostname (not an FQDN) is valid."""
    return re.match('^[a-zA-Z0-9-]+$', hostname) is not None


def is_valid_fqdn(fqdn):
    """Verify whether a host is a valid FQDN."""
    return re.match(r'^[a-zA-Z0-9.-]+\.[a-zA-Z]{2,}$', fqdn) is not None


def parse_valid_host_port(host_port):
    """
    Given a "host:port" string, attempts to parse it as intelligently as
    possible to determine if it is valid. This includes IPv6 [host]:port form,
    IPv4 ip:port form, and hostname:port or fqdn:port form.

    Invalid inputs will raise a ValueError, while valid inputs will return
    a (host, port) tuple where the port will always be of type int.
    """

    try:
        try:
            host, port = netutils.parse_host_port(host_port)
        except Exception:
            raise ValueError(_('Host and port "%s" is not valid.') % host_port)

        if not netutils.is_valid_port(port):
            raise ValueError(_('Port "%s" is not valid.') % port)

        # First check for valid IPv6 and IPv4 addresses, then a generic
        # hostname. Failing those, if the host includes a period, then this
        # should pass a very generic FQDN check. The FQDN check for letters at
        # the tail end will weed out any hilariously absurd IPv4 addresses.

        if not (netutils.is_valid_ipv6(host) or netutils.is_valid_ipv4(host) or
                is_valid_hostname(host) or is_valid_fqdn(host)):
            raise ValueError(_('Host "%s" is not valid.') % host)

    except Exception as ex:
        raise ValueError(_('%s '
                           'Please specify a host:port pair, where host is an '
                           'IPv4 address, IPv6 address, hostname, or FQDN. If '
                           'using an IPv6 address, enclose it in brackets '
                           'separately from the port (i.e., '
                           '"[fe80::a:b:c]:9876").') % ex)

    return (host, int(port))


try:
    REGEX_4BYTE_UNICODE = re.compile(u'[\U00010000-\U0010ffff]')
except re.error:
    # UCS-2 build case
    REGEX_4BYTE_UNICODE = re.compile(u'[\uD800-\uDBFF][\uDC00-\uDFFF]')


def no_4byte_params(f):
    """
    Checks that no 4 byte unicode characters are allowed
    in dicts' keys/values and string's parameters
    """

    def wrapper(*args, **kwargs):

        def _is_match(some_str):
            return (
                    isinstance(some_str, str) and
                    REGEX_4BYTE_UNICODE.findall(some_str) != []
            )

        def _check_dict(data_dict):
            # a dict of dicts has to be checked recursively
            for key, value in data_dict.items():
                if isinstance(value, dict):
                    _check_dict(value)
                else:
                    if _is_match(key):
                        msg = _("Property names can't contain 4 byte unicode.")
                        raise exception.Invalid(msg)
                    if _is_match(value):
                        msg = (_("%s can't contain 4 byte unicode characters.")
                               % key.title())
                        raise exception.Invalid(msg)

        for data_dict in [arg for arg in args if isinstance(arg, dict)]:
            _check_dict(data_dict)
        # now check args for str values
        for arg in args:
            if _is_match(arg):
                msg = _("Param values can't contain 4 byte unicode.")
                raise exception.Invalid(msg)
        # check kwargs as well, as params are passed as kwargs via
        # registry calls
        _check_dict(kwargs)
        return f(*args, **kwargs)

    return wrapper


def stash_conf_values():
    """
    Make a copy of some of the current global CONF's settings.
    Allows determining if any of these values have changed
    when the config is reloaded.
    """
    conf = {
        'bind_host': CONF.bind_host,
        'bind_port': CONF.bind_port,
        'backlog': CONF.backlog,
    }

    return conf


def split_filter_op(expression):
    """Split operator from threshold in an expression.
    Designed for use on a comparative-filtering query field.
    When no operator is found, default to an equality comparison.

    :param expression: the expression to parse

    :returns: a tuple (operator, threshold) parsed from expression
    """
    left, sep, right = expression.partition(':')
    if sep:
        # If the expression is a date of the format ISO 8601 like
        # CCYY-MM-DDThh:mm:ss+hh:mm and has no operator, it should
        # not be partitioned, and a default operator of eq should be
        # assumed.
        try:
            timeutils.parse_isotime(expression)
            op = 'eq'
            threshold = expression
        except ValueError:
            op = left
            threshold = right
    else:
        op = 'eq'  # default operator
        threshold = left

    # NOTE stevelle decoding escaped values may be needed later
    return op, threshold


def validate_quotes(value):
    """Validate filter values

    Validation opening/closing quotes in the expression.
    """
    open_quotes = True
    for i in range(len(value)):
        if value[i] == '"':
            if i and value[i - 1] == '\\':
                continue
            if open_quotes:
                if i and value[i - 1] != ',':
                    msg = _("Invalid filter value %s. There is no comma "
                            "before opening quotation mark.") % value
                    raise exception.InvalidParameterValue(message=msg)
            else:
                if i + 1 != len(value) and value[i + 1] != ",":
                    msg = _("Invalid filter value %s. There is no comma "
                            "after closing quotation mark.") % value
                    raise exception.InvalidParameterValue(message=msg)
            open_quotes = not open_quotes
    if not open_quotes:
        msg = _("Invalid filter value %s. The quote is not closed.") % value
        raise exception.InvalidParameterValue(message=msg)


def split_filter_value_for_quotes(value):
    """Split filter values

    Split values by commas and quotes for 'in' operator, according api-wg.
    """
    validate_quotes(value)
    tmp = re.compile(r'''
        "(                 # if found a double-quote
           [^\"\\]*        # take characters either non-quotes or backslashes
           (?:\\.          # take backslashes and character after it
            [^\"\\]*)*     # take characters either non-quotes or backslashes
         )                 # before double-quote
        ",?                # a double-quote with comma maybe
        | ([^,]+),?        # if not found double-quote take any non-comma
                           # characters with comma maybe
        | ,                # if we have only comma take empty string
        ''', re.VERBOSE)
    return [val[0] or val[1] for val in re.findall(tmp, value)]


def evaluate_filter_op(value, operator, threshold):
    """Evaluate a comparison operator.
    Designed for use on a comparative-filtering query field.

    :param value: evaluated against the operator, as left side of expression
    :param operator: any supported filter operation
    :param threshold: to compare value against, as right side of expression

    :raises InvalidFilterOperatorValue: if an unknown operator is provided

    :returns: boolean result of applied comparison

    """
    if operator == 'gt':
        return value > threshold
    elif operator == 'gte':
        return value >= threshold
    elif operator == 'lt':
        return value < threshold
    elif operator == 'lte':
        return value <= threshold
    elif operator == 'neq':
        return value != threshold
    elif operator == 'eq':
        return value == threshold

    msg = _("Unable to filter on a unknown operator.")
    raise exception.InvalidFilterOperatorValue(msg)


def attr_as_boolean(val_attr):
    """Return the boolean value, decoded from a string.

    We test explicitly for a value meaning False, which can be one of
    several formats as specified in oslo strutils.FALSE_STRINGS.
    All other string values (including an empty string) are treated as
    meaning True.

    """
    return strutils.bool_from_string(val_attr, default=True)
