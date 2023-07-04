# Copyright (c) 2023 WenRui Gong
# All rights reserved.

from oslo_serialization import jsonutils

from sqlalchemy import Boolean, Integer, String, Text
from sqlalchemy import Column
from sqlalchemy import ForeignKey
from sqlalchemy.orm import relationship

from everest.db.sqlalchemy.models.base import ModelBase, ModelDictMixin
from everest.db.sqlalchemy.models.base import JSONEncodedDict


class FederationProtocol(ModelBase, ModelDictMixin):
    __tablename__ = 'federation_protocol'
    attributes = ['id', 'idp_id', 'mapping_id', 'remote_id_attribute']
    mutable_attributes = frozenset(['mapping_id', 'remote_id_attribute'])

    id = Column(String(64), primary_key=True)
    idp_id = Column(String(64), ForeignKey('identity_provider.id',
                                           ondelete='CASCADE'), primary_key=True)
    mapping_id = Column(String(64), nullable=False)
    remote_id_attribute = Column(String(64))

    @classmethod
    def from_dict(cls, dictionary):
        new_dictionary = dictionary.copy()
        return cls(**new_dictionary)

    def to_dict(self):
        """Return a dictionary with model's attributes."""
        d = dict()
        for attr in self.__class__.attributes:
            d[attr] = getattr(self, attr)
        return d


class IdentityProvider(ModelBase, ModelDictMixin):
    __tablename__ = 'identity_provider'
    attributes = ['id', 'domain_id', 'enabled', 'description', 'remote_ids',
                  'authorization_ttl']
    mutable_attributes = frozenset(['description', 'enabled', 'remote_ids',
                                    'authorization_ttl'])

    id = Column(String(64), primary_key=True)
    domain_id = Column(String(64), nullable=False)
    enabled = Column(Boolean, nullable=False)
    description = Column(Text(), nullable=True)
    authorization_ttl = Column(Integer, nullable=True)

    remote_ids = relationship('IdPRemoteIds',
                              order_by='IdPRemoteIds.remote_id',
                              cascade='all, delete-orphan')
    expiring_user_group_memberships = relationship(
        'ExpiringUserGroupMembership',
        cascade='all, delete-orphan',
        backref="idp"
    )

    @classmethod
    def from_dict(cls, dictionary):
        new_dictionary = dictionary.copy()
        remote_ids_list = new_dictionary.pop('remote_ids', None)
        if not remote_ids_list:
            remote_ids_list = []
        identity_provider = cls(**new_dictionary)
        remote_ids = []
        # NOTE(fmarco76): the remote_ids_list contains only remote ids
        # associated with the IdP because of the "relationship" established in
        # sqlalchemy and corresponding to the FK in the idp_remote_ids table
        for remote in remote_ids_list:
            remote_ids.append(IdPRemoteIds(remote_id=remote))
        identity_provider.remote_ids = remote_ids
        return identity_provider

    def to_dict(self):
        """Return a dictionary with model's attributes."""
        d = dict()
        for attr in self.__class__.attributes:
            d[attr] = getattr(self, attr)
        d['remote_ids'] = []
        for remote in self.remote_ids:
            d['remote_ids'].append(remote.remote_id)
        return d


class IdPRemoteIds(ModelBase, ModelDictMixin):
    __tablename__ = 'idp_remote_ids'
    attributes = ['idp_id', 'remote_id']
    mutable_attributes = frozenset(['idp_id', 'remote_id'])

    idp_id = Column(String(64),
                    ForeignKey('identity_provider.id',
                               ondelete='CASCADE'))
    remote_id = Column(String(255),
                       primary_key=True)

    @classmethod
    def from_dict(cls, dictionary):
        new_dictionary = dictionary.copy()
        return cls(**new_dictionary)

    def to_dict(self):
        """Return a dictionary with model's attributes."""
        d = dict()
        for attr in self.__class__.attributes:
            d[attr] = getattr(self, attr)
        return d


class Mapping(ModelBase, ModelDictMixin):
    __tablename__ = 'mapping'
    attributes = ['id', 'rules']

    id = Column(String(64), primary_key=True)
    rules = Column(JSONEncodedDict(), default={}, nullable=False)

    @classmethod
    def from_dict(cls, dictionary):
        new_dictionary = dictionary.copy()
        new_dictionary['rules'] = jsonutils.dumps(new_dictionary['rules'])
        return cls(**new_dictionary)

    def to_dict(self):
        """Return a dictionary with model's attributes."""
        d = dict()
        for attr in self.__class__.attributes:
            d[attr] = getattr(self, attr)
        d['rules'] = jsonutils.loads(d['rules'])
        return d


class ServiceProvider(ModelBase, ModelDictMixin):
    __tablename__ = 'service_provider'
    attributes = ['auth_url', 'id', 'enabled', 'description',
                  'relay_state_prefix', 'sp_url']
    mutable_attributes = frozenset(['auth_url', 'description', 'enabled',
                                    'relay_state_prefix', 'sp_url'])

    id = Column(String(64), primary_key=True)
    enabled = Column(Boolean, nullable=False)
    description = Column(Text(), nullable=True)
    auth_url = Column(String(256), nullable=False)
    sp_url = Column(String(256), nullable=False)
    relay_state_prefix = Column(String(256), nullable=False)

    @classmethod
    def from_dict(cls, dictionary):
        new_dictionary = dictionary.copy()
        return cls(**new_dictionary)

    def to_dict(self):
        """Return a dictionary with model's attributes."""
        d = dict()
        for attr in self.__class__.attributes:
            d[attr] = getattr(self, attr)
        return d

