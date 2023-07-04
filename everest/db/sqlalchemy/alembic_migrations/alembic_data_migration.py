# Copyright 2016 Rackspace
# Copyright 2016 Intel Corporation
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

import importlib
import os.path
import pkgutil

from everest.common import exception
from everest.db import migration as db_migrations
from everest.db.sqlalchemy import api as db_api


def _find_migration_modules(release):
    migrations = list()
    for _, module_name, _ in pkgutil.iter_modules([os.path.dirname(__file__)]):
        if module_name.startswith(release):
            migrations.append(module_name)

    migration_modules = list()
    for migration in sorted(migrations):
        module = importlib.import_module('.'.join([__package__, migration]))
        has_migrations_function = getattr(module, 'has_migrations', None)
        migrate_function = getattr(module, 'migrate', None)

        if has_migrations_function is None or migrate_function is None:
            raise exception.InvalidDataMigrationScript(script=module.__name__)

        migration_modules.append(module)

    return migration_modules


def _run_migrations(engine, migrations):
    rows_migrated = 0
    for migration in migrations:
        if migration.has_migrations(engine):
            rows_migrated += migration.migrate(engine)

    return rows_migrated


def has_pending_migrations(engine=None, release=db_migrations.CURRENT_RELEASE):
    if not engine:
        engine = db_api.get_engine()

    migrations = _find_migration_modules(release)
    if not migrations:
        return False
    return any([x.has_migrations(engine) for x in migrations])


def migrate(engine=None, release=db_migrations.CURRENT_RELEASE):
    if not engine:
        engine = db_api.get_engine()

    migrations = _find_migration_modules(release)
    rows_migrated = _run_migrations(engine, migrations)
    return rows_migrated
