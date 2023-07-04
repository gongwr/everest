# Copyright (c) 2014 Hewlett-Packard Development Company, L.P.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.


from oslo_db import exception as db_exc
from oslo_log import log as logging
from sqlalchemy import func
from sqlalchemy.exc import NoResultFound

from everest.common import exception as exc
from everest.db.sqlalchemy.metadef_api import namespace as namespace_api
import everest.db.sqlalchemy.metadef_api.utils as metadef_utils
from everest.db.sqlalchemy.models import metadef as models
from everest.i18n import _

LOG = logging.getLogger(__name__)


def _get(context, object_id, session):
    try:
        query = session.query(models.MetadefObject).filter_by(id=object_id)
        metadef_object = query.one()
    except NoResultFound:
        msg = (_("Metadata definition object not found for id=%s")
               % object_id)
        LOG.warning(msg)
        raise exc.MetadefObjectNotFound(msg)

    return metadef_object


def _get_by_name(context, namespace_name, name, session):
    namespace = namespace_api.get(context, namespace_name, session)
    try:
        query = session.query(models.MetadefObject).filter_by(
            name=name, namespace_id=namespace['id'])
        metadef_object = query.one()
    except NoResultFound:
        LOG.debug("The metadata definition object with name=%(name)s"
                  " was not found in namespace=%(namespace_name)s.",
                  {'name': name, 'namespace_name': namespace_name})
        raise exc.MetadefObjectNotFound(object_name=name,
                                        namespace_name=namespace_name)

    return metadef_object


def get_all(context, namespace_name, session):
    namespace = namespace_api.get(context, namespace_name, session)
    query = session.query(models.MetadefObject).filter_by(
        namespace_id=namespace['id'])
    md_objects = query.all()

    md_objects_list = []
    for obj in md_objects:
        md_objects_list.append(obj.to_dict())
    return md_objects_list


def create(context, namespace_name, values, session):
    namespace = namespace_api.get(context, namespace_name, session)
    values.update({'namespace_id': namespace['id']})

    md_object = models.MetadefObject()
    metadef_utils.drop_protected_attrs(models.MetadefObject, values)
    md_object.update(values.copy())
    try:
        md_object.save(session=session)
    except db_exc.DBDuplicateEntry:
        LOG.debug("A metadata definition object with name=%(name)s"
                  " in namespace=%(namespace_name)s already exists.",
                  {'name': md_object.name,
                   'namespace_name': namespace_name})
        raise exc.MetadefDuplicateObject(
            object_name=md_object.name, namespace_name=namespace_name)

    return md_object.to_dict()


def get(context, namespace_name, name, session):
    md_object = _get_by_name(context, namespace_name, name, session)

    return md_object.to_dict()


def update(context, namespace_name, object_id, values, session):
    """Update an object, raise if ns not found/visible or duplicate result"""
    namespace_api.get(context, namespace_name, session)

    md_object = _get(context, object_id, session)
    metadef_utils.drop_protected_attrs(models.MetadefObject, values)
    # values['updated_at'] = timeutils.utcnow() - done by TS mixin
    try:
        md_object.update(values.copy())
        md_object.save(session=session)
    except db_exc.DBDuplicateEntry:
        LOG.debug("Invalid update. It would result in a duplicate"
                  " metadata definition object with same name=%(name)s"
                  " in namespace=%(namespace_name)s.",
                  {'name': md_object.name, 'namespace_name': namespace_name})
        emsg = (_("Invalid update. It would result in a duplicate"
                  " metadata definition object with the same name=%(name)s"
                  " in namespace=%(namespace_name)s.")
                % {'name': md_object.name, 'namespace_name': namespace_name})
        raise exc.MetadefDuplicateObject(emsg)

    return md_object.to_dict()


def delete(context, namespace_name, object_name, session):
    namespace_api.get(context, namespace_name, session)
    md_object = _get_by_name(context, namespace_name, object_name, session)

    session.delete(md_object)
    session.flush()

    return md_object.to_dict()


def delete_namespace_content(context, namespace_id, session):
    """Use this def only if the ns for the id has been verified as visible"""

    query = session.query(models.MetadefObject).filter_by(
        namespace_id=namespace_id)
    count = query.delete(synchronize_session='fetch')
    return count


def delete_by_namespace_name(context, namespace_name, session):
    namespace = namespace_api.get(context, namespace_name, session)
    return delete_namespace_content(context, namespace['id'], session)


def count(context, namespace_name, session):
    """Get the count of objects for a namespace, raise if ns not found"""
    namespace = namespace_api.get(context, namespace_name, session)

    query = session.query(func.count(models.MetadefObject.id)).filter_by(
        namespace_id=namespace['id'])
    return query.scalar()
