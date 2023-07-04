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

import errno
import functools
import os
import re
from time import sleep

from oslo_config import cfg
from oslo_log import log as logging
from oslo_utils import excutils, netutils, strutils
from webob import exc

from everest.common import exception
from everest.common import timeutils
from everest.i18n import _

CONF = cfg.CONF

LOG = logging.getLogger(__name__)


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
