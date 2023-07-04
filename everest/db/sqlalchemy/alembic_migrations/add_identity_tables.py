# Copyright (c) 2023 WenRui Gong
# All rights reserved.

import datetime

from alembic import op
from sqlalchemy import Boolean, DateTime, Date, Integer, String, Text
from sqlalchemy import Column
from sqlalchemy import ForeignKey, ForeignKeyConstraint, Index, UniqueConstraint

from everest.db.sqlalchemy.models.base import JSONEncodedDict, DateTimeInt


def _add_user_table():
    op.create_table(
        'user',
        Column('id', String(length=64), primary_key=True),
        Column('extra', JSONEncodedDict(), nullable=False),
        Column('enabled', Boolean()),
        Column('default_project_id', String(length=64)),
        Column('created_at', DateTime(), nullable=True),
        Column('last_active_at', Date(), nullable=True),
        Column('domain_id', String(length=64), nullable=False),
        UniqueConstraint('id', 'domain_id', name='ixu_user_id_domain_id'),
        Index('ix_default_project_id', 'default_project_id'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_local_user_table():
    op.create_table(
        'local_user',
        Column('id', Integer(), primary_key=True, nullable=False),
        Column('user_id', String(length=64), nullable=False, unique=True),
        Column('domain_id', String(length=64), nullable=False),
        Column('name', String(length=255), nullable=False),
        Column('failed_auth_count', Integer, nullable=True),
        Column('failed_auth_at', DateTime(), nullable=True),
        ForeignKeyConstraint(
            ["user_id", "domain_id"],
            ['user.id', 'user.domain_id'],
            name='local_user_user_id_fkey',
            onupdate='CASCADE',
            ondelete='CASCADE',
        ),
        UniqueConstraint('domain_id', 'name'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_password_table():
    op.create_table(
        'password',
        Column('id', Integer(), primary_key=True, nullable=False),
        Column('local_user_id', Integer(), ForeignKey('local_user.id', ondelete='CASCADE'), nullable=False),
        Column('expires_at', DateTime(), nullable=True),
        Column('self_service', Boolean(), nullable=False, server_default='0', default=False),
        # NOTE(notmorgan): To support the full range of scrypt and pbkfd
        # password hash lengths, this should be closer to varchar(1500) instead
        # of varchar(255).
        Column('password_hash', String(length=255), nullable=True),
        Column('created_at_int', DateTimeInt(), nullable=False, default=0, server_default='0'),
        Column('expires_at_int', DateTimeInt(), nullable=True),
        Column('created_at', DateTime(), nullable=False, default=datetime.datetime.utcnow),
    )


def _add_federated_user_table():
    op.create_table(
        'federated_user',
        Column('id', Integer, primary_key=True, nullable=False),
        Column('user_id', String(length=64), ForeignKey('user.id', ondelete='CASCADE'), nullable=False),
        Column('idp_id', String(length=64), ForeignKey('identity_provider.id', ondelete='CASCADE'),
               nullable=False),
        Column('protocol_id', String(length=64), nullable=False),
        Column('unique_id', String(length=255), nullable=False),
        Column('display_name', String(length=255), nullable=True),
        ForeignKeyConstraint(
            ['protocol_id', 'idp_id'],
            ['federation_protocol.id', 'federation_protocol.idp_id'],
            name='federated_user_protocol_id_fkey',
            ondelete='CASCADE',
        ),
        UniqueConstraint('idp_id', 'protocol_id', 'unique_id'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_nonlocal_users_table():
    op.create_table(
        'nonlocal_user',
        Column('domain_id', String(length=64), primary_key=True),
        Column('name', String(length=255), primary_key=True),
        Column('user_id', String(length=64), nullable=False),
        ForeignKeyConstraint(
            ['user_id', 'domain_id'],
            ['user.id', 'user.domain_id'],
            name='nonlocal_user_user_id_fkey',
            onupdate='CASCADE',
            ondelete='CASCADE',
        ),
        UniqueConstraint('user_id', name='ixu_nonlocal_user_user_id'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_group_table():
    op.create_table(
        'group',
        Column('id', String(length=64), primary_key=True),
        Column('domain_id', String(length=64), nullable=False),
        Column('name', String(length=64), nullable=False),
        Column('description', Text()),
        Column('extra', JSONEncodedDict(), default={}, nullable=False),
        UniqueConstraint(
            'domain_id',
            'name',
            name='ixu_group_name_domain_id',
        ),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_user_group_membership_table():
    op.create_table(
        'user_group_membership',
        Column('user_id', String(length=64), ForeignKey('user.id', name='fk_user_group_membership_user_id'),
               primary_key=True),
        Column('group_id', String(length=64), ForeignKey('group.id', name='fk_user_group_membership_group_id'),
               primary_key=True),
        # NOTE(stevemar): The index was named 'group_id' in
        # 050_fk_consistent_indexes.py and needs to be preserved
        Index('group_id', 'group_id'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_expiring_user_group_membership_table():
    op.create_table(
        'expiring_user_group_membership',
        Column('user_id', String(length=64), ForeignKey('user.id'), primary_key=True),
        Column('group_id', String(length=64), ForeignKey('group.id'), primary_key=True),
        Column('idp_id', String(length=64), ForeignKey('identity_provider.id', ondelete='CASCADE'), primary_key=True),
        Column('last_verified', DateTime(), nullable=False),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_user_option_table():
    op.create_table(
        'user_option',
        Column('user_id', String(length=64), ForeignKey('user.id', ondelete='CASCADE'), nullable=False,
               primary_key=True),
        Column('option_id', String(length=4), nullable=False, primary_key=True),
        Column('option_value', JSONEncodedDict(), nullable=True),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def upgrade():
    _add_group_table()
    _add_user_table()
    _add_user_group_membership_table()
    _add_user_option_table()
    _add_expiring_user_group_membership_table()
    _add_local_user_table()
    _add_nonlocal_users_table()
    _add_password_table()
    _add_federated_user_table()



