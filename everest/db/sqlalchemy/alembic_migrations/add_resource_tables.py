# Copyright (c) 2023 WenRui Gong
# All rights reserved.

from alembic import op
from sqlalchemy import Boolean, String, Text, Unicode
from sqlalchemy import Column
from sqlalchemy import ForeignKey, UniqueConstraint

from everest.db.sqlalchemy.models.base import JSONEncodedDict


def _add_project_table():
    op.create_table(
        'project',
        Column('id', String(length=64), primary_key=True),
        Column('name', String(length=64), nullable=False),
        Column('extra', JSONEncodedDict(), default={}, nullable=False),
        Column('description', Text),
        Column('enabled', Boolean),
        Column('domain_id', String(length=64),
               ForeignKey('project.id', name='project_domain_id_fkey'), nullable=False),
        Column('parent_id', String(64), ForeignKey('project.id', name='project_parent_id_fkey'),
               nullable=True),
        Column('is_domain', Boolean, nullable=False, server_default='0', default=False),
        UniqueConstraint('domain_id', 'name', name='ixu_project_name_domain_id'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_project_option_table():
    op.create_table(
        'project_option',
        Column('project_id', String(64), ForeignKey('project.id', ondelete='CASCADE'),
               nullable=False, primary_key=True),
        Column('option_id', String(4), nullable=False, primary_key=True),
        Column('option_value', JSONEncodedDict(), default={}, nullable=False),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_project_tag_table():
    # NOTE(lamt) To allow tag name to be case-sensitive for MySQL, the 'name'
    # column needs to use collation, which is incompatible with Postgresql.
    # Using unicode to mirror nova's server tag:
    # https://github.com/openstack/nova/blob/master/nova/db/sqlalchemy/models.py
    op.create_table(
        'project_tag',
        Column('project_id', String(64), ForeignKey('project.id', ondelete='CASCADE'),
               nullable=False, primary_key=True),
        Column('name', Unicode(255), nullable=False, primary_key=True),
        UniqueConstraint('project_id', 'name'),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def upgrade():
    _add_project_table()
    _add_project_option_table()
    _add_project_tag_table()
