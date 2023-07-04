# Copyright 2016 Rackspace
# Copyright 2013 Intel Corporation
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

import os

from alembic import config as alembic_config
from alembic import migration as alembic_migration
from alembic import script as alembic_script
from sqlalchemy import MetaData, Table

from everest.db.sqlalchemy import api as db_api


def get_alembic_config(engine=None):
    """Return a valid alembic config object"""
    ini_path = os.path.join(os.path.dirname(__file__), 'alembic.ini')
    config = alembic_config.Config(os.path.abspath(ini_path))
    if engine is None:
        engine = db_api.get_engine()
    # str(sqlalchemy.engine.url.URL) returns a RFC-1738 quoted URL.
    # This means that a password like "foo@" will be turned into
    # "foo%40".  This causes a problem for set_main_option() here
    # because that uses ConfigParser.set, which (by design) uses
    # *python* interpolation to write the string out ... where "%" is
    # the special python interpolation character!  Avoid this
    # mismatch by quoting all %'s for the set below.
    quoted_engine_url = str(engine.url).replace('%', '%%')
    config.set_main_option('sqlalchemy.url', quoted_engine_url)
    return config


def get_current_alembic_heads():
    """Return current heads (if any) from the alembic migration table"""
    engine = db_api.get_engine()
    with engine.connect() as conn:
        context = alembic_migration.MigrationContext.configure(conn)
        heads = context.get_current_heads()

        def update_alembic_version(old, new):
            """Correct alembic head in order to upgrade DB using EMC method.

            :param:old: Actual alembic head
            :param:new: Expected alembic head to be updated
            """
            meta = MetaData(engine)
            alembic_version = Table('alembic_version', meta, autoload=True)
            alembic_version.update().values(
                version_num=new).where(
                alembic_version.c.version_num == old).execute()

        if ("pike01" in heads):
            update_alembic_version("pike01", "pike_contract01")
        elif ("ocata01" in heads):
            update_alembic_version("ocata01", "ocata_contract01")

        heads = context.get_current_heads()
        return heads


def get_alembic_branch_head(branch):
    """Return head revision name for particular branch"""
    a_config = get_alembic_config()
    script = alembic_script.ScriptDirectory.from_config(a_config)
    return script.revision_map.get_current_head(branch)
