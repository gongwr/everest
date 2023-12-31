# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# All Rights Reserved.
#
# Copyright 2013 OpenStack Foundation
# Copyright 2013 Intel Corporation
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""Metadata setup commands."""

import threading

from oslo_config import cfg
from oslo_db import options as db_options
from stevedore import driver

from everest.db.sqlalchemy import api as db_api


_IMPL = None
_LOCK = threading.Lock()

db_options.set_defaults(cfg.CONF)


def get_backend():
    global _IMPL
    if _IMPL is None:
        with _LOCK:
            if _IMPL is None:
                _IMPL = driver.DriverManager(
                    "everest.database.metadata_backend",
                    cfg.CONF.database.backend).driver
    return _IMPL


def load_metadefs():
    """Read metadefinition files and insert data into the database"""
    return get_backend().db_load_metadefs(engine=db_api.get_engine(),
                                          metadata_path=None,
                                          merge=False,
                                          prefer_new=False,
                                          overwrite=False)


def unload_metadefs():
    """Unload metadefinitions from database"""
    return get_backend().db_unload_metadefs(engine=db_api.get_engine())


def export_metadefs():
    """Export metadefinitions from database to files"""
    return get_backend().db_export_metadefs(engine=db_api.get_engine(),
                                            metadata_path=None)
