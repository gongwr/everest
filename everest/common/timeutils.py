# Copyright 2011 OpenStack Foundation.
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""
Time related utilities and helper functions.
"""

import datetime

import iso8601
from oslo_utils import encodeutils

# ISO 8601 extended time format with microseconds
_ISO8601_TIME_FORMAT_SUBSECOND = '%Y-%m-%dT%H:%M:%S.%f'
_ISO8601_TIME_FORMAT = '%Y-%m-%dT%H:%M:%S'
PERFECT_TIME_FORMAT = _ISO8601_TIME_FORMAT_SUBSECOND


def isotime(at=None, subsecond=False):
    """Stringify time in ISO 8601 format."""
    if not at:
        at = utcnow()
    st = at.strftime(_ISO8601_TIME_FORMAT
                     if not subsecond
                     else _ISO8601_TIME_FORMAT_SUBSECOND)
    tz = at.tzinfo.tzname(None) if at.tzinfo else 'UTC'
    # Need to handle either iso8601 or python UTC format
    st += ('Z' if tz in ['UTC', 'UTC+00:00'] else tz)
    return st


def parse_isotime(timestr):
    """Parse time from ISO 8601 format."""
    try:
        return iso8601.parse_date(timestr)
    except iso8601.ParseError as e:
        raise ValueError(encodeutils.exception_to_unicode(e))
    except TypeError as e:
        raise ValueError(encodeutils.exception_to_unicode(e))


def utcnow(with_timezone=False):
    """Overridable version of utils.utcnow that can return a TZ-aware datetime.
    """
    if utcnow.override_time:
        try:
            return utcnow.override_time.pop(0)
        except AttributeError:
            return utcnow.override_time
    if with_timezone:
        return datetime.datetime.now(tz=iso8601.iso8601.UTC)
    return datetime.datetime.utcnow()


def normalize_time(timestamp):
    """Normalize time in arbitrary timezone to UTC naive object."""
    offset = timestamp.utcoffset()
    if offset is None:
        return timestamp
    return timestamp.replace(tzinfo=None) - offset


def iso8601_from_timestamp(timestamp, microsecond=False):
    """Returns an iso8601 formatted date from timestamp."""
    return isotime(datetime.datetime.utcfromtimestamp(timestamp), microsecond)


utcnow.override_time = None


def delta_seconds(before, after):
    """Return the difference between two timing objects.

    Compute the difference in seconds between two date, time, or
    datetime objects (as a float, to microsecond resolution).
    """
    delta = after - before
    return datetime.timedelta.total_seconds(delta)
