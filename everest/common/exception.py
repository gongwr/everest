# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""Everest exception subclasses"""

import http.client
import urllib.parse as urlparse

from oslo_config import cfg
from oslo_log import log
from oslo_utils import encodeutils

from everest.i18n import _

LOG = log.getLogger(__name__)
CONF = cfg.CONF

EVEREST_API_EXCEPTIONS = set([])

_FATAL_EXCEPTION_FORMAT_ERRORS = False


def _format_with_unicode_kwargs(msg_format, kwargs):
    try:
        return msg_format % kwargs
    except UnicodeDecodeError:
        try:
            kwargs = {k: encodeutils.safe_decode(v)
                      for k, v in kwargs.items()}
        except UnicodeDecodeError:
            # NOTE(jamielennox): This is the complete failure case
            # at least by showing the template we have some idea
            # of where the error is coming from
            return msg_format

        return msg_format % kwargs


class _EverestExceptionMeta(type):
    """Automatically Register the Exceptions in 'EVEREST_API_EXCEPTIONS' list.

    The `EVEREST_API_EXCEPTIONS` list is utilized by flask to register a
    handler to emit sane details when the exception occurs.
    """

    def __new__(mcs, name, bases, class_dict):
        """Create a new instance and register with EVEREST_API_EXCEPTIONS."""
        cls = type.__new__(mcs, name, bases, class_dict)
        EVEREST_API_EXCEPTIONS.add(cls)
        return cls


class Error(Exception, metaclass=_EverestExceptionMeta):
    """Base error class.

    Child classes should define an HTTP status code, title, and a
    message_format.

    """

    code = None
    title = None
    message_format = None

    def __init__(self, message=None, **kwargs):
        try:
            message = self._build_message(message, **kwargs)
        except KeyError:
            # if you see this warning in your logs, please raise a bug report
            if _FATAL_EXCEPTION_FORMAT_ERRORS:
                raise
            else:
                LOG.warning('missing exception kwargs (programmer error)')
                message = self.message_format

        super(Error, self).__init__(message)

    def _build_message(self, message, **kwargs):
        """Build and returns an exception message.

        :raises KeyError: given insufficient kwargs

        """
        if message:
            return message
        return _format_with_unicode_kwargs(self.message_format, kwargs)


class EverestException(Exception):
    """
    Base Everest Exception

    To correctly use this class, inherit from it and define
    a 'message' property. That message will get printf'd
    with the keyword arguments provided to the constructor.
    """
    message = _("An unknown exception occurred")

    def __init__(self, message=None, *args, **kwargs):
        if not message:
            message = self.message
        try:
            if kwargs:
                message = message % kwargs
        except Exception:
            if _FATAL_EXCEPTION_FORMAT_ERRORS:
                raise
            else:
                # at least get the core message out if something happened
                pass
        self.msg = message
        super(EverestException, self).__init__(message)


class RedirectException(Exception):
    def __init__(self, url):
        self.url = urlparse.urlparse(url)


class MissingCredentialError(EverestException):
    message = _("Missing required credential: %(required)s")


class BadAuthStrategy(EverestException):
    message = _("Incorrect auth strategy, expected \"%(expected)s\" but "
                "received \"%(received)s\"")


class NotFound(EverestException):
    message = _("An object with the specified identifier was not found.")


class BadStoreUri(EverestException):
    message = _("The Store URI was malformed.")


class Duplicate(EverestException):
    message = _("An object with the same identifier already exists.")


class Conflict(EverestException):
    message = _("An object with the same identifier is currently being "
                "operated on.")


class StorageQuotaFull(EverestException):
    message = _("The size of the data %(image_size)s will exceed the limit. "
                "%(remaining)s bytes remaining.")


class AuthBadRequest(EverestException):
    message = _("Connect error/bad request to Auth service at URL %(url)s.")


class AuthUrlNotFound(EverestException):
    message = _("Auth service at URL %(url)s not found.")


class AuthorizationFailure(EverestException):
    message = _("Authorization failed.")


class NotAuthenticated(EverestException):
    message = _("You are not authenticated.")


class UploadException(EverestException):
    message = _('Image upload problem: %s')


class Forbidden(EverestException):
    message = _("You are not authorized to complete %(action)s action.")


class ForbiddenPublicImage(Forbidden):
    message = _("You are not authorized to complete this action.")


class ProtectedImageDelete(Forbidden):
    message = _("Image %(image_id)s is protected and cannot be deleted.")


class ProtectedMetadefNamespaceDelete(Forbidden):
    message = _("Metadata definition namespace %(namespace)s is protected"
                " and cannot be deleted.")


class ProtectedMetadefNamespacePropDelete(Forbidden):
    message = _("Metadata definition property %(property_name)s is protected"
                " and cannot be deleted.")


class ProtectedMetadefObjectDelete(Forbidden):
    message = _("Metadata definition object %(object_name)s is protected"
                " and cannot be deleted.")


class ProtectedMetadefResourceTypeAssociationDelete(Forbidden):
    message = _("Metadata definition resource-type-association"
                " %(resource_type)s is protected and cannot be deleted.")


class ProtectedMetadefResourceTypeSystemDelete(Forbidden):
    message = _("Metadata definition resource-type %(resource_type_name)s is"
                " a seeded-system type and cannot be deleted.")


class ProtectedMetadefTagDelete(Forbidden):
    message = _("Metadata definition tag %(tag_name)s is protected"
                " and cannot be deleted.")


class Invalid(EverestException):
    message = _("Data supplied was not valid.")


class InvalidSortKey(Invalid):
    message = _("Sort key supplied was not valid.")


class InvalidSortDir(Invalid):
    message = _("Sort direction supplied was not valid.")


class InvalidPropertyProtectionConfiguration(Invalid):
    message = _("Invalid configuration in property protection file.")


class InvalidSwiftStoreConfiguration(Invalid):
    message = _("Invalid configuration in everest-swift conf file.")


class InvalidFilterOperatorValue(Invalid):
    message = _("Unable to filter using the specified operator.")


class InvalidFilterRangeValue(Invalid):
    message = _("Unable to filter using the specified range.")


class InvalidOptionValue(Invalid):
    message = _("Invalid value for option %(option)s: %(value)s")


class ReadonlyProperty(Forbidden):
    message = _("Attribute '%(property)s' is read-only.")


class ReservedProperty(Forbidden):
    message = _("Attribute '%(property)s' is reserved.")


class AuthorizationRedirect(EverestException):
    message = _("Redirecting to %(uri)s for authorization.")


class ClientConnectionError(EverestException):
    message = _("There was an error connecting to a server")


class ClientConfigurationError(EverestException):
    message = _("There was an error configuring the client.")


class MultipleChoices(EverestException):
    message = _("The request returned a 302 Multiple Choices. This generally "
                "means that you have not included a version indicator in a "
                "request URI.\n\nThe body of response returned:\n%(body)s")


class LimitExceeded(EverestException):
    message = _("The request returned a 413 Request Entity Too Large. This "
                "generally means that rate limiting or a quota threshold was "
                "breached.\n\nThe response body:\n%(body)s")

    def __init__(self, *args, **kwargs):
        self.retry_after = (int(kwargs['retry']) if kwargs.get('retry')
                            else None)
        super(LimitExceeded, self).__init__(*args, **kwargs)


class ServiceUnavailable(EverestException):
    message = _("The request returned 503 Service Unavailable. This "
                "generally occurs on service overload or other transient "
                "outage.")

    def __init__(self, *args, **kwargs):
        self.retry_after = (int(kwargs['retry']) if kwargs.get('retry')
                            else None)
        super(ServiceUnavailable, self).__init__(*args, **kwargs)


class ServerError(EverestException):
    message = _("The request returned 500 Internal Server Error.")


class UnexpectedStatus(EverestException):
    message = _("The request returned an unexpected status: %(status)s."
                "\n\nThe response body:\n%(body)s")


class InvalidContentType(EverestException):
    message = _("Invalid content type %(content_type)s")


class BadRegistryConnectionConfiguration(EverestException):
    message = _("Registry was not configured correctly on API server. "
                "Reason: %(reason)s")


class BadDriverConfiguration(EverestException):
    message = _("Driver %(driver_name)s could not be configured correctly. "
                "Reason: %(reason)s")


class MaxRedirectsExceeded(EverestException):
    message = _("Maximum redirects (%(redirects)s) was exceeded.")


class InvalidRedirect(EverestException):
    message = _("Received invalid HTTP redirect.")


class NoServiceEndpoint(EverestException):
    message = _("Response from Everest does not contain a Everest endpoint.")


class RegionAmbiguity(EverestException):
    message = _("Multiple 'image' service matches for region %(region)s. This "
                "generally means that a region is required and you have not "
                "supplied one.")


class WorkerCreationFailure(EverestException):
    message = _("Server worker creation failed: %(reason)s.")


class SchemaLoadError(EverestException):
    message = _("Unable to load schema: %(reason)s")


class InvalidObject(EverestException):
    message = _("Provided object does not match schema "
                "'%(schema)s': %(reason)s")


class ImageSizeLimitExceeded(EverestException):
    message = _("The provided image is too large.")


class FailedToGetScrubberJobs(EverestException):
    message = _("Scrubber encountered an error while trying to fetch "
                "scrub jobs.")


class ImageMemberLimitExceeded(LimitExceeded):
    message = _("The limit has been exceeded on the number of allowed image "
                "members for this image. Attempted: %(attempted)s, "
                "Maximum: %(maximum)s")


class ImagePropertyLimitExceeded(LimitExceeded):
    message = _("The limit has been exceeded on the number of allowed image "
                "properties. Attempted: %(attempted)s, Maximum: %(maximum)s")


class ImageTagLimitExceeded(LimitExceeded):
    message = _("The limit has been exceeded on the number of allowed image "
                "tags. Attempted: %(attempted)s, Maximum: %(maximum)s")


class ImageLocationLimitExceeded(LimitExceeded):
    message = _("The limit has been exceeded on the number of allowed image "
                "locations. Attempted: %(attempted)s, Maximum: %(maximum)s")


class SIGHUPInterrupt(EverestException):
    message = _("System SIGHUP signal received.")


class RPCError(EverestException):
    message = _("%(cls)s exception was raised in the last rpc call: %(val)s")


class TaskException(EverestException):
    message = _("An unknown task exception occurred")


class BadTaskConfiguration(EverestException):
    message = _("Task was not configured properly")


class ImageNotFound(NotFound):
    message = _("Image with the given id %(image_id)s was not found")


class TaskNotFound(TaskException, NotFound):
    message = _("Task with the given id %(task_id)s was not found")


class InvalidTaskStatus(TaskException, Invalid):
    message = _("Provided status of task is unsupported: %(status)s")


class InvalidTaskType(TaskException, Invalid):
    message = _("Provided type of task is unsupported: %(type)s")


class InvalidTaskStatusTransition(TaskException, Invalid):
    message = _("Status transition from %(cur_status)s to"
                " %(new_status)s is not allowed")


class ImportTaskError(TaskException, Invalid):
    message = _("An import task exception occurred")


class TaskAbortedError(ImportTaskError):
    message = _("Task was aborted externally")


class DuplicateLocation(Duplicate):
    message = _("The location %(location)s already exists")


class InvalidParameterValue(Invalid):
    message = _("Invalid value '%(value)s' for parameter '%(param)s': "
                "%(extra_msg)s")


class InvalidImageStatusTransition(Invalid):
    message = _("Image status transition from %(cur_status)s to"
                " %(new_status)s is not allowed")


class MetadefDuplicateNamespace(Duplicate):
    message = _("The metadata definition namespace=%(namespace_name)s"
                " already exists.")


class MetadefDuplicateObject(Duplicate):
    message = _("A metadata definition object with name=%(object_name)s"
                " already exists in namespace=%(namespace_name)s.")


class MetadefDuplicateProperty(Duplicate):
    message = _("A metadata definition property with name=%(property_name)s"
                " already exists in namespace=%(namespace_name)s.")


class MetadefDuplicateResourceType(Duplicate):
    message = _("A metadata definition resource-type with"
                " name=%(resource_type_name)s already exists.")


class MetadefDuplicateResourceTypeAssociation(Duplicate):
    message = _("The metadata definition resource-type association of"
                " resource-type=%(resource_type_name)s to"
                " namespace=%(namespace_name)s"
                " already exists.")


class MetadefDuplicateTag(Duplicate):
    message = _("A metadata tag with name=%(name)s"
                " already exists in namespace=%(namespace_name)s."
                " (Please note that metadata tag names are"
                " case insensitive).")


class MetadefForbidden(Forbidden):
    message = _("You are not authorized to complete this action.")


class MetadefIntegrityError(Forbidden):
    message = _("The metadata definition %(record_type)s with"
                " name=%(record_name)s not deleted."
                " Other records still refer to it.")


class MetadefNamespaceNotFound(NotFound):
    message = _("Metadata definition namespace=%(namespace_name)s"
                " was not found.")


class MetadefObjectNotFound(NotFound):
    message = _("The metadata definition object with"
                " name=%(object_name)s was not found in"
                " namespace=%(namespace_name)s.")


class MetadefPropertyNotFound(NotFound):
    message = _("The metadata definition property with"
                " name=%(property_name)s was not found in"
                " namespace=%(namespace_name)s.")


class MetadefResourceTypeNotFound(NotFound):
    message = _("The metadata definition resource-type with"
                " name=%(resource_type_name)s, was not found.")


class MetadefResourceTypeAssociationNotFound(NotFound):
    message = _("The metadata definition resource-type association of"
                " resource-type=%(resource_type_name)s to"
                " namespace=%(namespace_name)s,"
                " was not found.")


class MetadefTagNotFound(NotFound):
    message = _("The metadata definition tag with"
                " name=%(name)s was not found in"
                " namespace=%(namespace_name)s.")


class InvalidDataMigrationScript(EverestException):
    message = _("Invalid data migration script '%(script)s'. A valid data "
                "migration script must implement functions 'has_migrations' "
                "and 'migrate'.")


class ValidationError(Error):
    message_format = _("Expecting to find %(attribute)s in %(target)s."
                       " The server could not comply with the request"
                       " since it is either malformed or otherwise"
                       " incorrect. The client is assumed to be in error.")
    code = int(http.client.BAD_REQUEST)
    title = http.client.responses[http.client.BAD_REQUEST]


class ForbiddenNotSecurity(Error):
    """When you want to return a 403 Forbidden response but not security.
    Use this for errors where the message is always safe to present to the user
    and won't give away extra information.
    """
    code = int(http.client.FORBIDDEN)
    title = http.client.responses[http.client.FORBIDDEN]


class PasswordVerificationError(ForbiddenNotSecurity):
    message_format = _("The password length must be less than or equal "
                       "to %(size)i. The server could not comply with the "
                       "request because the password is invalid.")


class PasswordValidationError(ValidationError):
    message_format = _("Password validation error: %(detail)s.")


class PasswordRequirementsValidationError(PasswordValidationError):
    message_format = _("The password does not match the requirements:"
                       " %(detail)s.")


class SchemaValidationError(ValidationError):
    # NOTE(lbragstad): For whole OpenStack message consistency, this error
    # message has been written in a format consistent with WSME.
    message_format = _("%(detail)s")


class StringLengthExceeded(ValidationError):
    message_format = _("String length exceeded. The length of"
                       " string '%(string)s' exceeds the limit"
                       " of column %(type)s(CHAR(%(length)d)).")


class SecurityError(Error):
    """Security error exception.

    Avoids exposing details of security errors, unless in insecure_debug mode.

    """

    amendment = _('(Disable insecure_debug mode to suppress these details.)')

    def __deepcopy__(self):
        """Override the default deepcopy.

        Keystone :class:`keystone.exception.Error` accepts an optional message
        that will be used when rendering the exception object as a string. If
        not provided the object's message_format attribute is used instead.
        :class:`keystone.exception.SecurityError` is a little different in
        that it only uses the message provided to the initializer when
        keystone is in `insecure_debug` mode. Instead, it will use its
        `message_format`. This is to ensure that sensitive details are not
        leaked back to the caller in a production deployment.

        This dual mode for string rendering causes some odd behaviour when
        combined with oslo_i18n translation. Any object used as a value for
        formatting a translated string is deeply copied.

        The copy causes an issue. The deep copy process actually creates a new
        exception instance with the rendered string. Then when that new
        instance is rendered as a string to use for substitution a warning is
        logged. This is because the code tries to use the `message_format` in
        secure mode, but the required kwargs are not in the deep copy.

        The end result is not an error because when the KeyError is caught the
        instance's ``message`` is used instead and this has the properly
        translated message. The only indication that something is wonky is a
        message in the warning log.
        """
        return self

    def _build_message(self, message, **kwargs):
        """Only returns detailed messages in insecure_debug mode."""
        if message and CONF.insecure_debug:
            if isinstance(message, str):
                # Only do replacement if message is string. The message is
                # sometimes a different exception or bytes, which would raise
                # TypeError.
                message = _format_with_unicode_kwargs(message, kwargs)
            return _('%(message)s %(amendment)s') % {
                'message': message,
                'amendment': self.amendment}

        return _format_with_unicode_kwargs(self.message_format, kwargs)


class Unauthorized(SecurityError):
    message_format = _("The request you have made requires authentication.")
    code = int(http.client.UNAUTHORIZED)
    title = http.client.responses[http.client.UNAUTHORIZED]


class UnexpectedError(SecurityError):
    """Avoids exposing details of failures, unless in insecure_debug mode."""

    message_format = _("An unexpected error prevented the server "
                       "from fulfilling your request.")

    debug_message_format = _("An unexpected error prevented the server "
                             "from fulfilling your request: %(exception)s.")

    def _build_message(self, message, **kwargs):
        # Ensure that exception has a value to be extra defensive for
        # substitutions and make sure the exception doesn't raise an
        # exception.
        kwargs.setdefault('exception', '')

        return super(UnexpectedError, self)._build_message(
            message or self.debug_message_format, **kwargs)

    code = int(http.client.INTERNAL_SERVER_ERROR)
    title = http.client.responses[http.client.INTERNAL_SERVER_ERROR]
