# Copyright 2016 Rackspace
# Copyright 2013 Intel Corporation
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""alpha initial

Revision ID: alpha
Revises:
Create Date: 2016-08-03 16:06:59.657433

"""

from everest.db.sqlalchemy.alembic_migrations import add_metadefs_tables
from everest.db.sqlalchemy.alembic_migrations import add_role_tables
from everest.db.sqlalchemy.alembic_migrations import add_tasks_tables
from everest.db.sqlalchemy.alembic_migrations import add_identity_tables
from everest.db.sqlalchemy.alembic_migrations import add_federation_tables
from everest.db.sqlalchemy.alembic_migrations import add_resource_tables

# revision identifiers, used by Alembic.
revision = 'alpha'
down_revision = None
branch_labels = None
depends_on = None


def upgrade():
    add_federation_tables.upgrade()
    add_identity_tables.upgrade()
    add_metadefs_tables.upgrade()
    add_tasks_tables.upgrade()
    add_resource_tables.upgrade()
    add_role_tables.upgrade()
