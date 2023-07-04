# Copyright (c) 2023 WenRui Gong
# All rights reserved.


from alembic import op
from sqlalchemy import Column, Enum, MetaData

from everest.db import migration

# revision identifiers, used by Alembic.
revision = 'bravo_expand01'
down_revision = 'alpha'
branch_labels = migration.EXPAND_BRANCH
depends_on = None


def upgrade():
    pass
