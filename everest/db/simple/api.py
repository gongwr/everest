# Copyright 2012 OpenStack, Foundation
# Copyright 2013 IBM Corp.
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

import copy
import functools

from oslo_config import cfg
from oslo_log import log as logging

from everest.common import exception
from everest.common import timeutils
from everest.common import utils
from everest.i18n import _

CONF = cfg.CONF
LOG = logging.getLogger(__name__)

DATA = {
    'metadef_namespace_resource_types': [],
    'metadef_namespaces': [],
    'metadef_objects': [],
    'metadef_properties': [],
    'metadef_resource_types': [],
    'metadef_tags': [],
    'tasks': {},
    'task_info': {},
}

INDEX = 0


def log_call(func):
    @functools.wraps(func)
    def wrapped(*args, **kwargs):
        LOG.info('Calling %(funcname)s: args=%(args)s, kwargs=%(kwargs)s',
                 {"funcname": func.__name__,
                  "args": args,
                  "kwargs": kwargs})
        output = func(*args, **kwargs)
        LOG.info('Returning %(funcname)s: %(output)s',
                 {"funcname": func.__name__,
                  "output": output})
        return output

    return wrapped


def configure():
    if CONF.workers not in [0, 1]:
        msg = _('CONF.workers should be set to 0 or 1 when using the db.simple.api backend.'
                'Fore more info, see https://bugs.launchpad.net/everest/+bug/1619508')
        LOG.critical(msg)
        raise SystemExit(msg)


def reset():
    global DATA
    DATA = {
        'metadef_namespace_resource_types': [],
        'metadef_namespaces': [],
        'metadef_objects': [],
        'metadef_properties': [],
        'metadef_resource_types': [],
        'metadef_tags': [],
        'tasks': {},
        'task_info': {},
    }


def clear_db_env(*args, **kwargs):
    """
    Setup global environment configuration variables.

    We have no connection-oriented environment variables, so this is a NOOP.
    """
    pass


def _get_session():
    return DATA


def _metadef_delete_namespace_content(get_func, key, context, namespace_name):
    global DATA
    metadefs = get_func(context, namespace_name)
    data = DATA[key]
    for metadef in metadefs:
        data.remove(metadef)
    return metadefs


@log_call
@utils.no_4byte_params
def metadef_namespace_create(context, values):
    """Create a namespace object"""
    global DATA

    namespace_values = copy.deepcopy(values)
    namespace_name = namespace_values.get('namespace')
    required_attributes = ['namespace', 'owner']
    allowed_attributes = ['namespace', 'owner', 'display_name', 'description',
                          'visibility', 'protected']

    for namespace in DATA['metadef_namespaces']:
        if namespace['namespace'] == namespace_name:
            LOG.debug("Can not create the metadata definition namespace. "
                      "Namespace=%s already exists.", namespace_name)
            raise exception.MetadefDuplicateNamespace(
                namespace_name=namespace_name)

    for key in required_attributes:
        if key not in namespace_values:
            raise exception.Invalid('%s is a required attribute' % key)

    incorrect_keys = set(namespace_values.keys()) - set(allowed_attributes)
    if incorrect_keys:
        raise exception.Invalid(
            'The keys %s are not valid' % str(incorrect_keys))

    namespace = _format_namespace(namespace_values)
    DATA['metadef_namespaces'].append(namespace)

    return namespace


@log_call
@utils.no_4byte_params
def metadef_namespace_update(context, namespace_id, values):
    """Update a namespace object"""
    global DATA
    namespace_values = copy.deepcopy(values)

    namespace = metadef_namespace_get_by_id(context, namespace_id)
    if namespace['namespace'] != values['namespace']:
        for db_namespace in DATA['metadef_namespaces']:
            if db_namespace['namespace'] == values['namespace']:
                LOG.debug("Invalid update. It would result in a duplicate "
                          "metadata definition namespace with the same "
                          "name of %s", values['namespace'])
                emsg = (_("Invalid update. It would result in a duplicate"
                          " metadata definition namespace with the same"
                          " name of %s")
                        % values['namespace'])
                raise exception.MetadefDuplicateNamespace(emsg)
    DATA['metadef_namespaces'].remove(namespace)

    namespace.update(namespace_values)
    namespace['updated_at'] = timeutils.utcnow()
    DATA['metadef_namespaces'].append(namespace)

    return namespace


@log_call
def metadef_namespace_get_by_id(context, namespace_id):
    """Get a namespace object"""
    try:
        namespace = next(namespace for namespace in DATA['metadef_namespaces']
                         if namespace['id'] == namespace_id)
    except StopIteration:
        msg = (_("Metadata definition namespace not found for id=%s")
               % namespace_id)
        LOG.warning(msg)
        raise exception.MetadefNamespaceNotFound(msg)

    if not _is_namespace_visible(context, namespace):
        LOG.debug("Forbidding request, metadata definition namespace=%s "
                  "is not visible.", namespace.namespace)
        emsg = _("Forbidding request, metadata definition namespace=%s "
                 "is not visible.") % namespace.namespace
        raise exception.MetadefForbidden(emsg)

    return namespace


@log_call
def metadef_namespace_get(context, namespace_name):
    """Get a namespace object"""
    try:
        namespace = next(namespace for namespace in DATA['metadef_namespaces']
                         if namespace['namespace'] == namespace_name)
    except StopIteration:
        LOG.debug("No namespace found with name %s", namespace_name)
        raise exception.MetadefNamespaceNotFound(
            namespace_name=namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    return namespace


@log_call
def metadef_namespace_get_all(context,
                              marker=None,
                              limit=None,
                              sort_key='created_at',
                              sort_dir='desc',
                              filters=None):
    """Get a namespaces list"""
    resource_types = filters.get('resource_types', []) if filters else []
    visibility = filters.get('visibility') if filters else None

    namespaces = []
    for namespace in DATA['metadef_namespaces']:
        if not _is_namespace_visible(context, namespace):
            continue

        if visibility and namespace['visibility'] != visibility:
            continue

        if resource_types:
            for association in DATA['metadef_namespace_resource_types']:
                if association['namespace_id'] == namespace['id']:
                    if association['name'] in resource_types:
                        break
            else:
                continue

        namespaces.append(namespace)

    return namespaces


@log_call
def metadef_namespace_delete(context, namespace_name):
    """Delete a namespace object"""
    global DATA

    namespace = metadef_namespace_get(context, namespace_name)
    DATA['metadef_namespaces'].remove(namespace)

    return namespace


@log_call
def metadef_namespace_delete_content(context, namespace_name):
    """Delete a namespace content"""
    global DATA
    namespace = metadef_namespace_get(context, namespace_name)
    namespace_id = namespace['id']

    objects = []

    for object in DATA['metadef_objects']:
        if object['namespace_id'] != namespace_id:
            objects.append(object)

    DATA['metadef_objects'] = objects

    properties = []

    for property in DATA['metadef_objects']:
        if property['namespace_id'] != namespace_id:
            properties.append(object)

    DATA['metadef_objects'] = properties

    return namespace


@log_call
def metadef_object_get(context, namespace_name, object_name):
    """Get a metadef object"""
    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    for object in DATA['metadef_objects']:
        if (object['namespace_id'] == namespace['id'] and
                object['name'] == object_name):
            return object
    else:
        LOG.debug("The metadata definition object with name=%(name)s"
                  " was not found in namespace=%(namespace_name)s.",
                  {'name': object_name, 'namespace_name': namespace_name})
        raise exception.MetadefObjectNotFound(namespace_name=namespace_name,
                                              object_name=object_name)


@log_call
def metadef_object_get_by_id(context, namespace_name, object_id):
    """Get a metadef object"""
    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    for object in DATA['metadef_objects']:
        if (object['namespace_id'] == namespace['id'] and
                object['id'] == object_id):
            return object
    else:
        msg = (_("Metadata definition object not found for id=%s")
               % object_id)
        LOG.warning(msg)
        raise exception.MetadefObjectNotFound(msg)


@log_call
def metadef_object_get_all(context, namespace_name):
    """Get a metadef objects list"""
    namespace = metadef_namespace_get(context, namespace_name)

    objects = []

    _check_namespace_visibility(context, namespace, namespace_name)

    for object in DATA['metadef_objects']:
        if object['namespace_id'] == namespace['id']:
            objects.append(object)

    return objects


@log_call
@utils.no_4byte_params
def metadef_object_create(context, namespace_name, values):
    """Create a metadef object"""
    global DATA

    object_values = copy.deepcopy(values)
    object_name = object_values['name']
    required_attributes = ['name']
    allowed_attributes = ['name', 'description', 'json_schema', 'required']

    namespace = metadef_namespace_get(context, namespace_name)

    for object in DATA['metadef_objects']:
        if (object['name'] == object_name and
                object['namespace_id'] == namespace['id']):
            LOG.debug("A metadata definition object with name=%(name)s "
                      "in namespace=%(namespace_name)s already exists.",
                      {'name': object_name, 'namespace_name': namespace_name})
            raise exception.MetadefDuplicateObject(
                object_name=object_name, namespace_name=namespace_name)

    for key in required_attributes:
        if key not in object_values:
            raise exception.Invalid('%s is a required attribute' % key)

    incorrect_keys = set(object_values.keys()) - set(allowed_attributes)
    if incorrect_keys:
        raise exception.Invalid(
            'The keys %s are not valid' % str(incorrect_keys))

    object_values['namespace_id'] = namespace['id']

    _check_namespace_visibility(context, namespace, namespace_name)

    object = _format_object(object_values)
    DATA['metadef_objects'].append(object)

    return object


@log_call
@utils.no_4byte_params
def metadef_object_update(context, namespace_name, object_id, values):
    """Update a metadef object"""
    global DATA

    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    object = metadef_object_get_by_id(context, namespace_name, object_id)
    if object['name'] != values['name']:
        for db_object in DATA['metadef_objects']:
            if (db_object['name'] == values['name'] and
                    db_object['namespace_id'] == namespace['id']):
                LOG.debug("Invalid update. It would result in a duplicate "
                          "metadata definition object with same name=%(name)s "
                          "in namespace=%(namespace_name)s.",
                          {'name': object['name'],
                           'namespace_name': namespace_name})
                emsg = (_("Invalid update. It would result in a duplicate"
                          " metadata definition object with the same"
                          " name=%(name)s "
                          " in namespace=%(namespace_name)s.")
                        % {'name': object['name'],
                           'namespace_name': namespace_name})
                raise exception.MetadefDuplicateObject(emsg)
    DATA['metadef_objects'].remove(object)

    object.update(values)
    object['updated_at'] = timeutils.utcnow()
    DATA['metadef_objects'].append(object)

    return object


@log_call
def metadef_object_delete(context, namespace_name, object_name):
    """Delete a metadef object"""
    global DATA

    object = metadef_object_get(context, namespace_name, object_name)
    DATA['metadef_objects'].remove(object)

    return object


def metadef_object_delete_namespace_content(context, namespace_name,
                                            session=None):
    """Delete an object or raise if namespace or object doesn't exist."""
    return _metadef_delete_namespace_content(
        metadef_object_get_all, 'metadef_objects', context, namespace_name)


@log_call
def metadef_object_count(context, namespace_name):
    """Get metadef object count in a namespace"""
    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    count = 0
    for object in DATA['metadef_objects']:
        if object['namespace_id'] == namespace['id']:
            count = count + 1

    return count


@log_call
def metadef_property_count(context, namespace_name):
    """Get properties count in a namespace"""
    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    count = 0
    for property in DATA['metadef_properties']:
        if property['namespace_id'] == namespace['id']:
            count = count + 1

    return count


@log_call
@utils.no_4byte_params
def metadef_property_create(context, namespace_name, values):
    """Create a metadef property"""
    global DATA

    property_values = copy.deepcopy(values)
    property_name = property_values['name']
    required_attributes = ['name']
    allowed_attributes = ['name', 'description', 'json_schema', 'required']

    namespace = metadef_namespace_get(context, namespace_name)

    for property in DATA['metadef_properties']:
        if (property['name'] == property_name and
                property['namespace_id'] == namespace['id']):
            LOG.debug("Can not create metadata definition property. A property"
                      " with name=%(name)s already exists in"
                      " namespace=%(namespace_name)s.",
                      {'name': property_name,
                       'namespace_name': namespace_name})
            raise exception.MetadefDuplicateProperty(
                property_name=property_name,
                namespace_name=namespace_name)

    for key in required_attributes:
        if key not in property_values:
            raise exception.Invalid('%s is a required attribute' % key)

    incorrect_keys = set(property_values.keys()) - set(allowed_attributes)
    if incorrect_keys:
        raise exception.Invalid(
            'The keys %s are not valid' % str(incorrect_keys))

    property_values['namespace_id'] = namespace['id']

    _check_namespace_visibility(context, namespace, namespace_name)

    property = _format_property(property_values)
    DATA['metadef_properties'].append(property)

    return property


@log_call
@utils.no_4byte_params
def metadef_property_update(context, namespace_name, property_id, values):
    """Update a metadef property"""
    global DATA

    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    property = metadef_property_get_by_id(context, namespace_name, property_id)
    if property['name'] != values['name']:
        for db_property in DATA['metadef_properties']:
            if (db_property['name'] == values['name'] and
                    db_property['namespace_id'] == namespace['id']):
                LOG.debug("Invalid update. It would result in a duplicate"
                          " metadata definition property with the same"
                          " name=%(name)s"
                          " in namespace=%(namespace_name)s.",
                          {'name': property['name'],
                           'namespace_name': namespace_name})
                emsg = (_("Invalid update. It would result in a duplicate"
                          " metadata definition property with the same"
                          " name=%(name)s"
                          " in namespace=%(namespace_name)s.")
                        % {'name': property['name'],
                           'namespace_name': namespace_name})
                raise exception.MetadefDuplicateProperty(emsg)
    DATA['metadef_properties'].remove(property)

    property.update(values)
    property['updated_at'] = timeutils.utcnow()
    DATA['metadef_properties'].append(property)

    return property


@log_call
def metadef_property_get_all(context, namespace_name):
    """Get a metadef properties list"""
    namespace = metadef_namespace_get(context, namespace_name)

    properties = []

    _check_namespace_visibility(context, namespace, namespace_name)

    for property in DATA['metadef_properties']:
        if property['namespace_id'] == namespace['id']:
            properties.append(property)

    return properties


@log_call
def metadef_property_get_by_id(context, namespace_name, property_id):
    """Get a metadef property"""
    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    for property in DATA['metadef_properties']:
        if (property['namespace_id'] == namespace['id'] and
                property['id'] == property_id):
            return property
    else:
        msg = (_("Metadata definition property not found for id=%s")
               % property_id)
        LOG.warning(msg)
        raise exception.MetadefPropertyNotFound(msg)


@log_call
def metadef_property_get(context, namespace_name, property_name):
    """Get a metadef property"""
    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    for property in DATA['metadef_properties']:
        if (property['namespace_id'] == namespace['id'] and
                property['name'] == property_name):
            return property
    else:
        LOG.debug("No property found with name=%(name)s in"
                  " namespace=%(namespace_name)s ",
                  {'name': property_name, 'namespace_name': namespace_name})
        raise exception.MetadefPropertyNotFound(namespace_name=namespace_name,
                                                property_name=property_name)


@log_call
def metadef_property_delete(context, namespace_name, property_name):
    """Delete a metadef property"""
    global DATA

    property = metadef_property_get(context, namespace_name, property_name)
    DATA['metadef_properties'].remove(property)

    return property


def metadef_property_delete_namespace_content(context, namespace_name,
                                              session=None):
    """Delete a property or raise if it or namespace doesn't exist."""
    return _metadef_delete_namespace_content(
        metadef_property_get_all, 'metadef_properties', context,
        namespace_name)


@log_call
def metadef_resource_type_create(context, values):
    """Create a metadef resource type"""
    global DATA

    resource_type_values = copy.deepcopy(values)
    resource_type_name = resource_type_values['name']

    allowed_attrubites = ['name', 'protected']

    for resource_type in DATA['metadef_resource_types']:
        if resource_type['name'] == resource_type_name:
            raise exception.Duplicate()

    incorrect_keys = set(resource_type_values.keys()) - set(allowed_attrubites)
    if incorrect_keys:
        raise exception.Invalid(
            'The keys %s are not valid' % str(incorrect_keys))

    resource_type = _format_resource_type(resource_type_values)
    DATA['metadef_resource_types'].append(resource_type)

    return resource_type


@log_call
def metadef_resource_type_get_all(context):
    """List all resource types"""
    return DATA['metadef_resource_types']


@log_call
def metadef_resource_type_get(context, resource_type_name):
    """Get a resource type"""
    try:
        resource_type = next(resource_type for resource_type in
                             DATA['metadef_resource_types']
                             if resource_type['name'] ==
                             resource_type_name)
    except StopIteration:
        LOG.debug("No resource type found with name %s", resource_type_name)
        raise exception.MetadefResourceTypeNotFound(
            resource_type_name=resource_type_name)

    return resource_type


@log_call
def metadef_resource_type_association_create(context, namespace_name,
                                             values):
    global DATA

    association_values = copy.deepcopy(values)

    namespace = metadef_namespace_get(context, namespace_name)
    resource_type_name = association_values['name']
    resource_type = metadef_resource_type_get(context,
                                              resource_type_name)

    required_attributes = ['name', 'properties_target', 'prefix']
    allowed_attributes = copy.deepcopy(required_attributes)

    for association in DATA['metadef_namespace_resource_types']:
        if (association['namespace_id'] == namespace['id'] and
                association['resource_type'] == resource_type['id']):
            LOG.debug("The metadata definition resource-type association of"
                      " resource_type=%(resource_type_name)s to"
                      " namespace=%(namespace_name)s, already exists.",
                      {'resource_type_name': resource_type_name,
                       'namespace_name': namespace_name})
            raise exception.MetadefDuplicateResourceTypeAssociation(
                resource_type_name=resource_type_name,
                namespace_name=namespace_name)

    for key in required_attributes:
        if key not in association_values:
            raise exception.Invalid('%s is a required attribute' % key)

    incorrect_keys = set(association_values.keys()) - set(allowed_attributes)
    if incorrect_keys:
        raise exception.Invalid(
            'The keys %s are not valid' % str(incorrect_keys))

    association = _format_association(namespace, resource_type,
                                      association_values)
    DATA['metadef_namespace_resource_types'].append(association)

    return association


@log_call
def metadef_resource_type_association_get(context, namespace_name,
                                          resource_type_name):
    namespace = metadef_namespace_get(context, namespace_name)
    resource_type = metadef_resource_type_get(context, resource_type_name)

    for association in DATA['metadef_namespace_resource_types']:
        if (association['namespace_id'] == namespace['id'] and
                association['resource_type'] == resource_type['id']):
            return association
    else:
        LOG.debug("No resource type association found associated with "
                  "namespace %s and resource type %s", namespace_name,
                  resource_type_name)
        raise exception.MetadefResourceTypeAssociationNotFound(
            resource_type_name=resource_type_name,
            namespace_name=namespace_name)


@log_call
def metadef_resource_type_association_get_all_by_namespace(context,
                                                           namespace_name):
    namespace = metadef_namespace_get(context, namespace_name)

    namespace_resource_types = []
    for resource_type in DATA['metadef_namespace_resource_types']:
        if resource_type['namespace_id'] == namespace['id']:
            namespace_resource_types.append(resource_type)

    return namespace_resource_types


@log_call
def metadef_resource_type_association_delete(context, namespace_name,
                                             resource_type_name):
    global DATA

    resource_type = metadef_resource_type_association_get(context,
                                                          namespace_name,
                                                          resource_type_name)
    DATA['metadef_namespace_resource_types'].remove(resource_type)

    return resource_type


@log_call
def metadef_tag_get(context, namespace_name, name):
    """Get a metadef tag"""
    namespace = metadef_namespace_get(context, namespace_name)
    _check_namespace_visibility(context, namespace, namespace_name)

    for tag in DATA['metadef_tags']:
        if tag['namespace_id'] == namespace['id'] and tag['name'] == name:
            return tag
    else:
        LOG.debug("The metadata definition tag with name=%(name)s"
                  " was not found in namespace=%(namespace_name)s.",
                  {'name': name, 'namespace_name': namespace_name})
        raise exception.MetadefTagNotFound(name=name,
                                           namespace_name=namespace_name)


@log_call
def metadef_tag_get_by_id(context, namespace_name, id):
    """Get a metadef tag"""
    namespace = metadef_namespace_get(context, namespace_name)
    _check_namespace_visibility(context, namespace, namespace_name)

    for tag in DATA['metadef_tags']:
        if tag['namespace_id'] == namespace['id'] and tag['id'] == id:
            return tag
    else:
        msg = (_("Metadata definition tag not found for id=%s") % id)
        LOG.warning(msg)
        raise exception.MetadefTagNotFound(msg)


@log_call
def metadef_tag_get_all(context, namespace_name, filters=None, marker=None,
                        limit=None, sort_key='created_at', sort_dir=None,
                        session=None):
    """Get a metadef tags list"""

    namespace = metadef_namespace_get(context, namespace_name)
    _check_namespace_visibility(context, namespace, namespace_name)

    tags = []
    for tag in DATA['metadef_tags']:
        if tag['namespace_id'] == namespace['id']:
            tags.append(tag)

    return tags


@log_call
@utils.no_4byte_params
def metadef_tag_create(context, namespace_name, values):
    """Create a metadef tag"""
    global DATA

    tag_values = copy.deepcopy(values)
    tag_name = tag_values['name']
    required_attributes = ['name']
    allowed_attributes = ['name']

    namespace = metadef_namespace_get(context, namespace_name)

    for tag in DATA['metadef_tags']:
        if tag['name'] == tag_name and tag['namespace_id'] == namespace['id']:
            LOG.debug("A metadata definition tag with name=%(name)s"
                      " in namespace=%(namespace_name)s already exists.",
                      {'name': tag_name, 'namespace_name': namespace_name})
            raise exception.MetadefDuplicateTag(
                name=tag_name, namespace_name=namespace_name)

    for key in required_attributes:
        if key not in tag_values:
            raise exception.Invalid('%s is a required attribute' % key)

    incorrect_keys = set(tag_values.keys()) - set(allowed_attributes)
    if incorrect_keys:
        raise exception.Invalid(
            'The keys %s are not valid' % str(incorrect_keys))

    tag_values['namespace_id'] = namespace['id']

    _check_namespace_visibility(context, namespace, namespace_name)

    tag = _format_tag(tag_values)
    DATA['metadef_tags'].append(tag)
    return tag


@log_call
def metadef_tag_create_tags(context, namespace_name, tag_list,
                            can_append=False):
    """Create a metadef tag"""
    global DATA

    namespace = metadef_namespace_get(context, namespace_name)
    _check_namespace_visibility(context, namespace, namespace_name)

    required_attributes = ['name']
    allowed_attributes = ['name']
    data_tag_list = []
    tag_name_list = []
    if can_append:
        # NOTE(mrjoshi): We need to fetch existing tags here for duplicate
        # check while adding new one
        tag_name_list = [tag['name']
                         for tag in metadef_tag_get_all(context,
                                                        namespace_name)]
    for tag_value in tag_list:
        tag_values = copy.deepcopy(tag_value)
        tag_name = tag_values['name']

        for key in required_attributes:
            if key not in tag_values:
                raise exception.Invalid('%s is a required attribute' % key)

        incorrect_keys = set(tag_values.keys()) - set(allowed_attributes)
        if incorrect_keys:
            raise exception.Invalid(
                'The keys %s are not valid' % str(incorrect_keys))

        if tag_name in tag_name_list:
            LOG.debug("A metadata definition tag with name=%(name)s"
                      " in namespace=%(namespace_name)s already exists.",
                      {'name': tag_name, 'namespace_name': namespace_name})
            raise exception.MetadefDuplicateTag(
                name=tag_name, namespace_name=namespace_name)
        else:
            tag_name_list.append(tag_name)

        tag_values['namespace_id'] = namespace['id']
        data_tag_list.append(_format_tag(tag_values))
    if not can_append:
        DATA['metadef_tags'] = []
    for tag in data_tag_list:
        DATA['metadef_tags'].append(tag)

    return data_tag_list


@log_call
@utils.no_4byte_params
def metadef_tag_update(context, namespace_name, id, values):
    """Update a metadef tag"""
    global DATA

    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    tag = metadef_tag_get_by_id(context, namespace_name, id)
    if tag['name'] != values['name']:
        for db_tag in DATA['metadef_tags']:
            if (db_tag['name'] == values['name'] and
                    db_tag['namespace_id'] == namespace['id']):
                LOG.debug("Invalid update. It would result in a duplicate"
                          " metadata definition tag with same name=%(name)s "
                          " in namespace=%(namespace_name)s.",
                          {'name': tag['name'],
                           'namespace_name': namespace_name})
                raise exception.MetadefDuplicateTag(
                    name=tag['name'], namespace_name=namespace_name)

    DATA['metadef_tags'].remove(tag)

    tag.update(values)
    tag['updated_at'] = timeutils.utcnow()
    DATA['metadef_tags'].append(tag)
    return tag


@log_call
def metadef_tag_delete(context, namespace_name, name):
    """Delete a metadef tag"""
    global DATA

    tags = metadef_tag_get(context, namespace_name, name)
    DATA['metadef_tags'].remove(tags)

    return tags


def metadef_tag_delete_namespace_content(context, namespace_name,
                                         session=None):
    """Delete an tag or raise if namespace or tag doesn't exist."""
    return _metadef_delete_namespace_content(
        metadef_tag_get_all, 'metadef_tags', context, namespace_name)


@log_call
def metadef_tag_count(context, namespace_name):
    """Get metadef tag count in a namespace"""
    namespace = metadef_namespace_get(context, namespace_name)

    _check_namespace_visibility(context, namespace, namespace_name)

    count = 0
    for tag in DATA['metadef_tags']:
        if tag['namespace_id'] == namespace['id']:
            count = count + 1

    return count


def _format_association(namespace, resource_type, association_values):
    association = {
        'namespace_id': namespace['id'],
        'resource_type': resource_type['id'],
        'properties_target': None,
        'prefix': None,
        'created_at': timeutils.utcnow(),
        'updated_at': timeutils.utcnow()

    }
    association.update(association_values)
    return association


def _format_resource_type(values):
    dt = timeutils.utcnow()
    resource_type = {
        'id': _get_metadef_id(),
        'name': values['name'],
        'protected': True,
        'created_at': dt,
        'updated_at': dt
    }
    resource_type.update(values)
    return resource_type


def _format_property(values):
    property = {
        'id': _get_metadef_id(),
        'namespace_id': None,
        'name': None,
        'json_schema': None
    }
    property.update(values)
    return property


def _format_namespace(values):
    dt = timeutils.utcnow()
    namespace = {
        'id': _get_metadef_id(),
        'namespace': None,
        'display_name': None,
        'description': None,
        'visibility': 'private',
        'protected': False,
        'owner': None,
        'created_at': dt,
        'updated_at': dt
    }
    namespace.update(values)
    return namespace


def _format_object(values):
    dt = timeutils.utcnow()
    object = {
        'id': _get_metadef_id(),
        'namespace_id': None,
        'name': None,
        'description': None,
        'json_schema': None,
        'required': None,
        'created_at': dt,
        'updated_at': dt
    }
    object.update(values)
    return object


def _format_tag(values):
    dt = timeutils.utcnow()
    tag = {
        'id': _get_metadef_id(),
        'namespace_id': None,
        'name': None,
        'created_at': dt,
        'updated_at': dt
    }
    tag.update(values)
    return tag


def _is_namespace_visible(context, namespace):
    """Return true if namespace is visible in this context"""
    if context.is_admin:
        return True

    if namespace.get('visibility', '') == 'public':
        return True

    if namespace['owner'] is None:
        return True

    if context.owner is not None:
        if context.owner == namespace['owner']:
            return True

    return False


def _check_namespace_visibility(context, namespace, namespace_name):
    if not _is_namespace_visible(context, namespace):
        LOG.debug("Forbidding request, metadata definition namespace=%s "
                  "is not visible.", namespace_name)
        emsg = _("Forbidding request, metadata definition namespace=%s"
                 " is not visible.") % namespace_name
        raise exception.MetadefForbidden(emsg)


def _get_metadef_id():
    global INDEX
    INDEX += 1
    return INDEX
