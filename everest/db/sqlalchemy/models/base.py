# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""
SQLAlchemy models for everest data
"""

import datetime

import pytz
from oslo_config import cfg
from oslo_log import log
from oslo_db import options as db_options
from oslo_db.sqlalchemy import models
from oslo_serialization import jsonutils
from osprofiler import opts as profiler

from sqlalchemy import Column
from sqlalchemy import BigInteger, Boolean, DateTime, String, Text
from sqlalchemy.ext import declarative
from sqlalchemy.types import TypeDecorator
from sqlalchemy.orm.attributes import InstrumentedAttribute

from everest.common import exception
from everest.common import timeutils
from everest.i18n import _

CONF = cfg.CONF
LOG = log.getLogger(__name__)

ModelBase = declarative.declarative_base()


def initialize():
    """Initialize the module."""
    db_options.set_defaults(
        CONF,
        connection="sqlite:///everest.db")
    # Configure OSprofiler options
    profiler.set_defaults(CONF, enabled=False, trace_sqlalchemy=False)


def initialize_decorator(init):
    """Ensure that the length of string field do not exceed the limit.

    This decorator check the initializer arguments, to make sure the
    length of string field do not exceed the length limit, or raise a
    'StringLengthExceeded' exception.

    Use decorator instead of inheritance, because the metaclass will
    check the __tablename__, primary key columns, etc. at the class
    definition.

    """

    def initialize(self, *args, **kwargs):
        cls = type(self)
        for k, v in kwargs.items():
            if hasattr(cls, k):
                attr = getattr(cls, k)
                if isinstance(attr, InstrumentedAttribute):
                    column = attr.property.columns[0]
                    if isinstance(column.type, String):
                        if not isinstance(v, str):
                            v = str(v)
                        if column.type.length and column.type.length < len(v):
                            raise exception.StringLengthExceeded(
                                string=v, type=k, length=column.type.length)

        init(self, *args, **kwargs)

    return initialize


ModelBase.__init__ = initialize_decorator(ModelBase.__init__)

NULL_DOMAIN_ID = '<<null>>'


class EverestBase(models.ModelBase, models.TimestampMixin):
    """Base class for Everest Models."""

    __table_args__ = {'mysql_engine': 'InnoDB', 'mysql_charset': 'utf8'}
    __table_initialized__ = False
    __protected_attributes__ = {"created_at", "updated_at", "deleted_at", "deleted"}

    def save(self, session=None):
        from everest.db.sqlalchemy import api as db_api
        super(EverestBase, self).save(session or db_api.get_session())

    created_at = Column(DateTime, default=lambda: timeutils.utcnow(),
                        nullable=False)
    # TODO(vsergeyev): Column `updated_at` have no default value in
    #                  OpenStack common code. We should decide, is this value
    #                  required and make changes in oslo (if required) or
    #                  in everest (if not).
    updated_at = Column(DateTime, default=lambda: timeutils.utcnow(),
                        nullable=True, onupdate=lambda: timeutils.utcnow())
    # TODO(boris-42): Use SoftDeleteMixin instead of deleted Column after
    #                 migration that provides UniqueConstraints and change
    #                 type of this column.
    deleted_at = Column(DateTime)
    deleted = Column(Boolean, nullable=False, default=False)

    def delete(self, session=None):
        """Delete this object."""
        self.deleted = True
        self.deleted_at = timeutils.utcnow()
        self.save(session=session)

    def keys(self):
        return self.__dict__.keys()

    def values(self):
        return self.__dict__.values()

    def items(self):
        return self.__dict__.items()

    def to_dict(self):
        d = self.__dict__.copy()
        # NOTE(flaper87): Remove
        # private state instance
        # It is not serializable
        # and causes CircularReference
        d.pop("_sa_instance_state")
        return d


class DateTimeInt(TypeDecorator):
    """A column that automatically converts a datetime object to an Int.

    Everest relies on accurate (sub-second) datetime objects. In some cases
    the RDBMS drop sub-second accuracy (some versions of MySQL). This field
    automatically converts the value to an INT when storing the data and
    back to a datetime object when it is loaded from the database.

    NOTE: Any datetime object that has timezone data will be converted to UTC.
          Any datetime object that has no timezone data will be assumed to be
          UTC and loaded from the DB as such.
    """

    impl = BigInteger
    epoch = datetime.datetime.fromtimestamp(0, tz=pytz.UTC)
    # NOTE(ralonsoh): set to True as any other TypeDecorator in SQLAlchemy
    # https://docs.sqlalchemy.org/en/14/core/custom_types.html# \
    #   sqlalchemy.types.TypeDecorator.cache_ok
    cache_ok = True
    """This type is safe to cache."""

    def process_bind_param(self, value, dialect):
        if value is None:
            return value
        else:
            if not isinstance(value, datetime.datetime):
                raise ValueError(_('Programming Error: value to be stored '
                                   'must be a datetime object.'))
            value = timeutils.normalize_time(value)
            value = value.replace(tzinfo=pytz.UTC)
            # NOTE(morgan): We are casting this to an int, and ensuring we
            # preserve microsecond data by moving the decimal. This is easier
            # than being concerned with the differences in Numeric types in
            # different SQL backends.
            return int((value - self.epoch).total_seconds() * 1000000)

    def process_result_value(self, value, dialect):
        if value is None:
            return None
        else:
            # Convert from INT to appropriate micro-second float (microseconds
            # after the decimal) from what was stored to the DB
            value = float(value) / 1000000
            # NOTE(morgan): Explictly use timezone "pytz.UTC" to ensure we are
            # not adjusting the actual datetime object from what we stored.
            dt_obj = datetime.datetime.fromtimestamp(value, tz=pytz.UTC)
            # Return non-tz aware datetime object (as everest expects)
            return timeutils.normalize_time(dt_obj)


class JSONEncodedDict(TypeDecorator):
    """Represents an immutable structure as a json-encoded string"""

    impl = Text

    cache_ok = True

    def process_bind_param(self, value, dialect):
        if value is not None:
            value = jsonutils.dumps(value)
        return value

    def process_result_value(self, value, dialect):
        if value is not None:
            value = jsonutils.loads(value)
        return value


class ModelDictMixin(models.ModelBase):

    @classmethod
    def from_dict(cls, d):
        """Return a model instance from a dictionary."""
        return cls(**d)

    def to_dict(self):
        """Return the model's attributes as a dictionary."""
        names = (column.name for column in self.__table__.columns)
        return {name: getattr(self, name) for name in names}


class ModelDictMixinWithExtras(models.ModelBase):
    """Mixin making model behave with dict-like interfaces includes extras.

    NOTE: DO NOT USE THIS FOR FUTURE SQL MODELS. "Extra" column is a legacy
          concept that should not be carried forward with new SQL models
          as the concept of "arbitrary" properties is not in line with
          the design philosophy of Everest.
    """

    attributes = []
    _msg = ('Programming Error: Model does not have an "extra" column. '
            'Unless the model already has an "extra" column and has '
            'existed in a previous released version of everest with '
            'the extra column included, the model should use '
            '"ModelDictMixin" instead.')

    @classmethod
    def from_dict(cls, d):
        new_d = d.copy()

        if not hasattr(cls, 'extra'):
            # NOTE(notmorgan): No translation here, This is an error for
            # programmers NOT end users.
            raise AttributeError(cls._msg)  # no qa

        new_d['extra'] = {k: new_d.pop(k) for k in d.keys()
                          if k not in cls.attributes and k != 'extra'}

        return cls(**new_d)

    def to_dict(self, include_extra_dict=False):
        """Return the model's attributes as a dictionary.

        If include_extra_dict is True, 'extra' attributes are literally
        included in the resulting dictionary twice, for backwards-compatibility
        with a broken implementation.

        """
        if not hasattr(self, 'extra'):
            # NOTE(notmorgan): No translation here, This is an error for
            # programmers NOT end users.
            raise AttributeError(self._msg)  # no qa

        d = self.extra.copy()
        for attr in self.__class__.attributes:
            d[attr] = getattr(self, attr)

        if include_extra_dict:
            d['extra'] = self.extra.copy()

        return d

    def __getitem__(self, key):
        """Evaluate if key is in extra or not, to return correct item."""
        if key in self.extra:
            return self.extra[key]
        return getattr(self, key)
