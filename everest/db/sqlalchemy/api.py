# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# Copyright 2010-2011 OpenStack Foundation
# Copyright 2012 Justin Santa Barbara
# Copyright 2013 IBM Corp.
# Copyright 2015 Mirantis, Inc.
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.


"""Defines interface for DB access."""

import datetime
import threading

import osprofiler.sqlalchemy
import sqlalchemy
import sqlalchemy.sql as sa_sql
from oslo_config import cfg
from oslo_db import exception as db_exception
from oslo_db.sqlalchemy import session
from oslo_log import log as logging
from oslo_utils import excutils
from sqlalchemy import MetaData, Table
from sqlalchemy import sql
from sqlalchemy.ext.compiler import compiles

from everest.common import exception
from everest.common import timeutils
from everest.db.sqlalchemy import models
from everest.i18n import _

sa_logger = None
LOG = logging.getLogger(__name__)

STATUSES = ['active', 'saving', 'queued', 'killed', 'pending_delete',
            'deleted', 'deactivated', 'importing', 'uploading']

CONF = cfg.CONF
CONF.import_group("profiler", "everest.common.wsgi")

_FACADE = None
_LOCK = threading.Lock()


def _create_facade_lazily():
    global _LOCK, _FACADE
    if _FACADE is None:
        with _LOCK:
            if _FACADE is None:
                _FACADE = session.EngineFacade.from_config(CONF)

                if CONF.profiler.enabled and CONF.profiler.trace_sqlalchemy:
                    osprofiler.sqlalchemy.add_tracing(sqlalchemy,
                                                      _FACADE.get_engine(),
                                                      "db")
    return _FACADE


def get_engine():
    facade = _create_facade_lazily()
    return facade.get_engine()


def get_session(autocommit=True, expire_on_commit=False):
    facade = _create_facade_lazily()
    engine = get_engine()
    return facade.get_session(bind=engine,
                              autocommit=False,
                              autoflush=False,
                              future=True)


def _validate_db_int(**kwargs):
    """Make sure that all arguments are less than or equal to 2 ** 31 - 1.

    This limitation is introduced because databases stores INT in 4 bytes.
    If the validation fails for some argument, exception.Invalid is raised with
    appropriate information.
    """
    max_int = (2 ** 31) - 1

    for param_key, param_value in kwargs.items():
        if param_value and param_value > max_int:
            msg = _("'%(param)s' value out of range, "
                    "must not exceed %(max)d.") % {"param": param_key,
                                                   "max": max_int}
            raise exception.Invalid(msg)


def clear_db_env():
    """
    Unset global configuration variables for database.
    """
    global _FACADE
    _FACADE = None


class DeleteFromSelect(sa_sql.expression.UpdateBase):
    def __init__(self, table, select, column):
        self.table = table
        self.select = select
        self.column = column


# NOTE(abhishekk): MySQL doesn't yet support subquery with
# 'LIMIT & IN/ALL/ANY/SOME' We need work around this with nesting select.
@compiles(DeleteFromSelect)
def visit_delete_from_select(element, compiler, **kw):
    return "DELETE FROM %s WHERE %s in (SELECT T1.%s FROM (%s) as T1)" % (
        compiler.process(element.table, asfrom=True),
        compiler.process(element.column),
        element.column.name,
        compiler.process(element.select))


def purge_deleted_rows(context, age_in_days, max_rows, session=None):
    """Purges soft deleted rows

    Deletes rows of table images, table tasks and all dependent tables
    according to given age for relevant models.
    """
    # check max_rows for its maximum limit
    _validate_db_int(max_rows=max_rows)

    session = session or get_session()
    metadata = MetaData(get_engine())
    deleted_age = timeutils.utcnow() - datetime.timedelta(days=age_in_days)

    tables = []
    for model_class in models.__dict__.values():
        if not hasattr(model_class, '__tablename__'):
            continue
        if hasattr(model_class, 'deleted'):
            tables.append(model_class.__tablename__)

    # First force purging of records that are not soft deleted but
    # are referencing soft deleted tasks/images records (e.g. task_info
    # records). Then purge all soft deleted records in everest tables in the
    # right order to avoid FK constraint violation.
    t = Table("tasks", metadata, autoload=True)
    ti = Table("task_info", metadata, autoload=True)
    joined_rec = ti.join(t, t.c.id == ti.c.task_id)
    deleted_task_info = sql. \
        select([ti.c.task_id], t.c.deleted_at < deleted_age). \
        select_from(joined_rec). \
        order_by(t.c.deleted_at)
    if max_rows != -1:
        deleted_task_info = deleted_task_info.limit(max_rows)
    delete_statement = DeleteFromSelect(ti, deleted_task_info,
                                        ti.c.task_id)
    LOG.info('Purging deleted rows older than %(age_in_days)d day(s) '
             'from table %(tbl)s',
             {'age_in_days': age_in_days, 'tbl': ti})
    try:
        with session.begin():
            result = session.execute(delete_statement)
    except (db_exception.DBError, db_exception.DBReferenceError) as ex:
        LOG.exception('DBError detected when force purging '
                      'table=%(table)s: %(error)s',
                      {'table': ti, 'error': str(ex)})
        raise

    rows = result.rowcount
    LOG.info('Deleted %(rows)d row(s) from table %(tbl)s',
             {'rows': rows, 'tbl': ti})

    # get rid of FK constraints
    for tbl in ('images', 'tasks'):
        try:
            tables.remove(tbl)
        except ValueError:
            LOG.warning('Expected table %(tbl)s was not found in DB.',
                        {'tbl': tbl})
        else:
            # NOTE(abhishekk): To mitigate OSSN-0075 images records should be
            # purged with new ``purge-images-table`` command.
            if tbl == 'images':
                continue

            tables.append(tbl)

    for tbl in tables:
        tab = Table(tbl, metadata, autoload=True)
        LOG.info('Purging deleted rows older than %(age_in_days)d day(s) '
                 'from table %(tbl)s',
                 {'age_in_days': age_in_days, 'tbl': tbl})

        column = tab.c.id
        deleted_at_column = tab.c.deleted_at

        query_delete = sql.select([column], deleted_at_column < deleted_age). \
            order_by(deleted_at_column)
        if max_rows != -1:
            query_delete = query_delete.limit(max_rows)

        delete_statement = DeleteFromSelect(tab, query_delete, column)

        try:
            with session.begin():
                result = session.execute(delete_statement)
        except db_exception.DBReferenceError as ex:
            with excutils.save_and_reraise_exception():
                LOG.error('DBError detected when purging from '
                          "%(tablename)s: %(error)s",
                          {'tablename': tbl, 'error': str(ex)})

        rows = result.rowcount
        LOG.info('Deleted %(rows)d row(s) from table %(tbl)s',
                 {'rows': rows, 'tbl': tbl})
