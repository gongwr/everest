# Copyright 2016 Rackspace
# Copyright 2013 Intel Corporation
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

from alembic import op
from sqlalchemy import String, DateTime, Boolean, Text
from sqlalchemy.schema import (
    Column, PrimaryKeyConstraint, ForeignKeyConstraint)

from everest.db.sqlalchemy.models.base import JSONEncodedDict


def _add_tasks_table():
    op.create_table('tasks',
                    Column('id', String(length=36), nullable=False),
                    Column('type', String(length=30), nullable=False),
                    Column('status', String(length=30), nullable=False),
                    Column('owner', String(length=256), nullable=False),
                    Column('expires_at', DateTime(), nullable=True),
                    Column('created_at', DateTime(), nullable=False),
                    Column('updated_at', DateTime(), nullable=True),
                    Column('deleted_at', DateTime(), nullable=True),
                    Column('deleted', Boolean(), nullable=False),
                    PrimaryKeyConstraint('id'),
                    mysql_engine='InnoDB',
                    mysql_charset='utf8',
                    extend_existing=True)

    op.create_index('ix_tasks_deleted', 'tasks', ['deleted'], unique=False)
    op.create_index('ix_tasks_owner', 'tasks', ['owner'], unique=False)
    op.create_index('ix_tasks_status', 'tasks', ['status'], unique=False)
    op.create_index('ix_tasks_type', 'tasks', ['type'], unique=False)
    op.create_index('ix_tasks_updated_at',
                    'tasks',
                    ['updated_at'],
                    unique=False)


def _add_task_info_table():
    op.create_table('task_info',
                    Column('task_id', String(length=36), nullable=False),
                    Column('input', JSONEncodedDict(), nullable=True),
                    Column('result', JSONEncodedDict(), nullable=True),
                    Column('message', Text(), nullable=True),
                    ForeignKeyConstraint(['task_id'], ['tasks.id'], ),
                    PrimaryKeyConstraint('task_id'),
                    mysql_engine='InnoDB',
                    mysql_charset='utf8',
                    extend_existing=True)


def upgrade():
    _add_tasks_table()
    _add_task_info_table()
