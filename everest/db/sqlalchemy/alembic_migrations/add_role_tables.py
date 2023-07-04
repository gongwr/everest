# Copyright (c) 2023 WenRui Gong
# All rights reserved.

from alembic import op
from sqlalchemy import Column
from sqlalchemy import ForeignKey, UniqueConstraint
from sqlalchemy import String

from everest.db.sqlalchemy.models.base import JSONEncodedDict, NULL_DOMAIN_ID


def _add_role_table():
    op.create_table(
        'role',
        Column('id', String(length=64), primary_key=True),
        Column('name', String(length=255), nullable=False),
        Column('extra', JSONEncodedDict, default={}, nullable=True),
        Column('domain_id', String(64), nullable=False, server_default=NULL_DOMAIN_ID),
        Column('description', String(255), nullable=True),
        UniqueConstraint('name', 'domain_id', name='ixu_role_name_domain_id'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_implied_role_table():
    op.create_table(
        'implied_role',
        Column('prior_role_id', String(length=64),
               ForeignKey('role.id', name='implied_role_prior_role_id_fkey', ondelete='CASCADE'),
               primary_key=True),
        Column('implied_role_id', String(length=64),
               ForeignKey('role.id', name='implied_role_implied_role_id_fkey', ondelete='CASCADE'),
               primary_key=True),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_role_option_table():
    op.create_table(
        'role_option',
        Column('role_id', String(64), ForeignKey('role.id', ondelete='CASCADE'), nullable=False,
               primary_key=True),
        Column('option_id', String(4), nullable=False, primary_key=True),
        Column('option_value', JSONEncodedDict, default={}, nullable=True),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def upgrade():
    _add_role_table()
    _add_implied_role_table()
    _add_role_option_table()
