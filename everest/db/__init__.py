# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# Copyright 2010-2012 OpenStack Foundation
# Copyright 2013 IBM Corp.
# Copyright 2015 Mirantis, Inc.
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

from oslo_config import cfg
from oslo_utils import importutils

CONF = cfg.CONF
CONF.import_opt('image_size_cap', 'everest.common.config')
CONF.import_opt('metadata_encryption_key', 'everest.common.config')


def get_api():
    api = importutils.import_module('everest.db.sqlalchemy.api')

    if hasattr(api, 'configure'):
        api.configure()

    return api


def unwrap(db_api):
    return db_api


# attributes common to all models
BASE_MODEL_ATTRS = {'id', 'created_at', 'updated_at', 'deleted_at', 'deleted'}
