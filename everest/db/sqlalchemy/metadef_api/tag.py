# Copyright (c) 2014 Hewlett-Packard Development Company, L.P.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.


from oslo_db import exception as db_exc
from oslo_db.sqlalchemy.utils import paginate_query
from oslo_log import log as logging
from sqlalchemy import func
from sqlalchemy.exc import NoResultFound

from everest.common import exception as exc
from everest.db.sqlalchemy.metadef_api import namespace as namespace_api
import everest.db.sqlalchemy.metadef_api.utils as metadef_utils
from everest.db.sqlalchemy.models import metadef as models

LOG = logging.getLogger(__name__)


def _get(context, id, session):
    try:
        query = (session.query(models.MetadefTag).filter_by(id=id))
        metadef_tag = query.one()
    except NoResultFound:
        msg = ("Metadata tag not found for id %s" % id)
        LOG.warning(msg)
        raise exc.MetadefTagNotFound(message=msg)
    return metadef_tag


def _get_by_name(context, namespace_name, name, session):
    namespace = namespace_api.get(context, namespace_name, session)
    try:
        query = (session.query(models.MetadefTag).filter_by(
            name=name, namespace_id=namespace['id']))
        metadef_tag = query.one()
    except NoResultFound:
        LOG.debug("The metadata tag with name=%(name)s"
                  " was not found in namespace=%(namespace_name)s.",
                  {'name': name, 'namespace_name': namespace_name})
        raise exc.MetadefTagNotFound(name=name,
                                     namespace_name=namespace_name)
    return metadef_tag


def get_all(context, namespace_name, session, filters=None, marker=None,
            limit=None, sort_key='created_at', sort_dir='desc'):
    """Get all tags that match zero or more filters.

    :param session:
    :param context:
    :param namespace_name:
    :param filters: dict of filter keys and values.
    :param marker: tag id after which to start page
    :param limit: maximum number of namespaces to return
    :param sort_key: namespace attribute by which results should be sorted
    :param sort_dir: direction in which results should be sorted (asc, desc)
    """

    namespace = namespace_api.get(context, namespace_name, session)
    query = (session.query(models.MetadefTag).filter_by(
        namespace_id=namespace['id']))

    marker_tag = None
    if marker is not None:
        marker_tag = _get(context, marker, session)

    sort_keys = ['created_at', 'id']
    sort_keys.insert(0, sort_key) if sort_key not in sort_keys else sort_keys

    query = paginate_query(query=query,
                           model=models.MetadefTag,
                           limit=limit,
                           sort_keys=sort_keys,
                           marker=marker_tag, sort_dir=sort_dir)
    metadef_tag = query.all()
    metadef_tag_list = []
    for tag in metadef_tag:
        metadef_tag_list.append(tag.to_dict())

    return metadef_tag_list


def create(context, namespace_name, values, session):
    namespace = namespace_api.get(context, namespace_name, session)
    values.update({'namespace_id': namespace['id']})

    metadef_tag = models.MetadefTag()
    metadef_utils.drop_protected_attrs(models.MetadefTag, values)
    metadef_tag.update(values.copy())
    try:
        metadef_tag.save(session=session)
    except db_exc.DBDuplicateEntry:
        LOG.debug("A metadata tag name=%(name)s"
                  " already exists in namespace=%(namespace_name)s."
                  " (Please note that metadata tag names are"
                  " case insensitive).",
                  {'name': metadef_tag.name,
                   'namespace_name': namespace_name})
        raise exc.MetadefDuplicateTag(
            name=metadef_tag.name, namespace_name=namespace_name)

    return metadef_tag.to_dict()


def create_tags(context, namespace_name, tag_list, can_append, session):

    metadef_tags_list = []
    if tag_list:
        namespace = namespace_api.get(context, namespace_name, session)

        try:
            with session.begin():
                if not can_append:
                    query = (session.query(models.MetadefTag).filter_by(
                             namespace_id=namespace['id']))
                    query.delete(synchronize_session='fetch')
                for value in tag_list:
                    value.update({'namespace_id': namespace['id']})
                    metadef_utils.drop_protected_attrs(
                        models.MetadefTag, value)
                    metadef_tag = models.MetadefTag()
                    metadef_tag.update(value.copy())
                    metadef_tag.save(session=session)
                    metadef_tags_list.append(metadef_tag.to_dict())
        except db_exc.DBDuplicateEntry:
            LOG.debug("A metadata tag name=%(name)s"
                      " in namespace=%(namespace_name)s already exists.",
                      {'name': metadef_tag.name,
                       'namespace_name': namespace_name})
            raise exc.MetadefDuplicateTag(
                name=metadef_tag.name, namespace_name=namespace_name)

    return metadef_tags_list


def get(context, namespace_name, name, session):
    metadef_tag = _get_by_name(context, namespace_name, name, session)
    return metadef_tag.to_dict()


def update(context, namespace_name, id, values, session):
    """Update a tag, raise if ns not found/visible or duplicate result"""
    namespace_api.get(context, namespace_name, session)

    metadata_tag = _get(context, id, session)
    metadef_utils.drop_protected_attrs(models.MetadefTag, values)
    # values['updated_at'] = timeutils.utcnow() - done by TS mixin
    try:
        metadata_tag.update(values.copy())
        metadata_tag.save(session=session)
    except db_exc.DBDuplicateEntry:
        LOG.debug("Invalid update. It would result in a duplicate"
                  " metadata tag with same name=%(name)s"
                  " in namespace=%(namespace_name)s.",
                  {'name': values['name'],
                   'namespace_name': namespace_name})
        raise exc.MetadefDuplicateTag(
            name=values['name'], namespace_name=namespace_name)

    return metadata_tag.to_dict()


def delete(context, namespace_name, name, session):
    namespace_api.get(context, namespace_name, session)
    md_tag = _get_by_name(context, namespace_name, name, session)

    session.delete(md_tag)
    session.flush()

    return md_tag.to_dict()


def delete_namespace_content(context, namespace_id, session):
    """Use this def only if the ns for the id has been verified as visible"""
    query = (session.query(models.MetadefTag).filter_by(
        namespace_id=namespace_id))
    count1 = query.delete(synchronize_session='fetch')
    return count1


def delete_by_namespace_name(context, namespace_name, session):
    namespace = namespace_api.get(context, namespace_name, session)
    return delete_namespace_content(context, namespace['id'], session)


def count(context, namespace_name, session):
    """Get the count of objects for a namespace, raise if ns not found"""
    namespace = namespace_api.get(context, namespace_name, session)
    query = (session.query(func.count(models.MetadefTag.id)).filter_by(
        namespace_id=namespace['id']))
    return query.scalar()
