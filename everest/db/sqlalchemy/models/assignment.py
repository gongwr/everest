# Copyright (c) 2023 WenRui Gong
# All rights reserved.

from sqlalchemy import Column
from sqlalchemy import ForeignKey, UniqueConstraint
from sqlalchemy import String
from sqlalchemy.orm import collections, relationship

from everest.common import resource_options
from everest.common.resource_options import role_resource_option as rro
from everest.db.sqlalchemy.models.base import ModelBase, NULL_DOMAIN_ID
from everest.db.sqlalchemy.models.base import JSONEncodedDict
from everest.db.sqlalchemy.models.base import ModelDictMixin, ModelDictMixinWithExtras


class RoleTable(ModelBase, ModelDictMixinWithExtras):

    def to_dict(self, include_extra_dict=False):
        d = super(RoleTable, self).to_dict(
            include_extra_dict=include_extra_dict)
        if d['domain_id'] == NULL_DOMAIN_ID:
            d['domain_id'] = None
        # NOTE(notmorgan): Eventually it may make sense to drop the empty
        # option dict creation to the superclass (if enough models use it)
        d['options'] = resource_options.ref_mapper_to_dict_options(self)
        return d

    @classmethod
    def from_dict(cls, role_dict):
        if 'domain_id' in role_dict and role_dict['domain_id'] is None:
            new_dict = role_dict.copy()
            new_dict['domain_id'] = NULL_DOMAIN_ID
        else:
            new_dict = role_dict
        # TODO(morgan): move this functionality to a common location
        resource_options = {}
        options = new_dict.pop('options', {})
        for opt in cls.resource_options_registry.options:
            if opt.option_name in options:
                opt_value = options[opt.option_name]
                # NOTE(notmorgan): None is always a valid type
                if opt_value is not None:
                    opt.validator(opt_value)
                resource_options[opt.option_id] = opt_value
        role_obj = super(RoleTable, cls).from_dict(new_dict)
        setattr(role_obj, '_resource_options', resource_options)
        return role_obj

    __tablename__ = 'role'
    attributes = ['id', 'name', 'domain_id', 'description']
    resource_options_registry = rro.ROLE_OPTIONS_REGISTRY
    id = Column(String(64), primary_key=True)
    name = Column(String(255), nullable=False)
    domain_id = Column(String(64), nullable=False,
                       server_default=NULL_DOMAIN_ID)
    description = Column(String(255), nullable=True)
    extra = Column(JSONEncodedDict, default={}, nullable=True)
    _resource_option_mapper = relationship(
        'RoleOption',
        single_parent=True,
        cascade='all,delete,delete-orphan',
        lazy='subquery',
        backref='role',
        collection_class=collections.attribute_mapped_collection('option_id')
    )
    __table_args__ = (UniqueConstraint('name', 'domain_id'),)


class ImpliedRoleTable(ModelBase, ModelDictMixin):
    __tablename__ = 'implied_role'
    attributes = ['prior_role_id', 'implied_role_id']
    prior_role_id = Column(
        String(64),
        ForeignKey('role.id', ondelete="CASCADE"),
        primary_key=True)
    implied_role_id = Column(
        String(64),
        ForeignKey('role.id', ondelete="CASCADE"),
        primary_key=True)

    @classmethod
    def from_dict(cls, dictionary):
        new_dictionary = dictionary.copy()
        return cls(**new_dictionary)

    def to_dict(self):
        """Return a dictionary with model's attributes.

        overrides the `to_dict` function from the base class
        to avoid having an `extra` field.
        """
        d = dict()
        for attr in self.__class__.attributes:
            d[attr] = getattr(self, attr)
        return d


class RoleOption(ModelBase):
    __tablename__ = 'role_option'
    role_id = Column(String(64),
                     ForeignKey('role.id', ondelete='CASCADE'),
                     nullable=False, primary_key=True)
    option_id = Column(String(4), nullable=False,
                       primary_key=True)
    option_value = Column(JSONEncodedDict, default={}, nullable=True)

    def __init__(self, option_id, option_value):
        self.option_id = option_id
        self.option_value = option_value
