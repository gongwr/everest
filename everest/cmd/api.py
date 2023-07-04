#!/usr/bin/env python

# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# Copyright 2011 OpenStack Foundation
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""
Everest API Server
"""

import os
import sys

import uvicorn
from oslo_reports import guru_meditation_report as gmr
from oslo_utils import encodeutils

# If ../everest/__init__.py exists, add ../ to Python search path, so that
# it will override what happens to be installed in /usr/(local/)lib/python...
BASE_PATH = os.path.normpath(
    os.path.join(os.path.abspath(__file__), os.pardir, os.pardir, os.pardir))
STATIC_PATH = os.path.join(BASE_PATH, 'static')

if os.path.exists(os.path.join(BASE_PATH, 'everest', '__init__.py')):
    sys.path.insert(0, BASE_PATH)

from oslo_config import cfg
from oslo_log import log as logging
import osprofiler.initializer

from fastapi import FastAPI, APIRouter
from fastapi.openapi.docs import get_redoc_html
from fastapi.staticfiles import StaticFiles

from everest.api.api_v1.api import api_router
from everest.common import config
from everest.common import exception
from everest.common import wsgi
from everest import version

CONF = cfg.CONF
CONF.import_group("profiler", "everest.common.wsgi")
logging.register_options(CONF)
wsgi.register_cli_opts()

# NOTE(rosmaita): Any new exceptions added should preserve the current
# error codes for backward compatibility.  The value 99 is returned
# for errors not listed in this map.
ERROR_CODE_MAP = {RuntimeError: 1,
                  exception.WorkerCreationFailure: 2,
                  ValueError: 3,
                  cfg.ConfigFileValueError: 4}


def fail(e):
    sys.stderr.write("ERROR: %s\n" % encodeutils.exception_to_unicode(e))
    return_code = ERROR_CODE_MAP.get(type(e), 99)
    sys.exit(return_code)


def create_everest():
    try:
        config.parse_args()
        config.set_config_defaults()
        logging.setup(CONF, 'everest')
        gmr.TextGuruMeditation.setup_autorun(version)

        if CONF.profiler.enabled:
            osprofiler.initializer.init_from_conf(
                conf=CONF,
                context={},
                project="everest",
                service="api",
                host=CONF.bind_host
            )

        if CONF.enforce_secure_rbac != CONF.oslo_policy.enforce_new_defaults:
            fail_message = (
                "[DEFAULT] enforce_secure_rbac does not match "
                "[oslo_policy] enforce_new_defaults. Please set both to "
                "True to enable secure RBAC personas. Otherwise, make sure "
                "both are False.")
            raise exception.ServerError(fail_message)

        root_router = APIRouter()
        app = FastAPI(title="Roraima API Server",
                      openapi_url="/api/v1/openapi.json",
                      docs_url=None, redoc_url=None)
        app.mount('/static', StaticFiles(directory=STATIC_PATH), name='static')

        @root_router.get("/")
        async def root():
            return {"message": "Hello World"}

        @root_router.get("/hello/{name}")
        async def say_hello(name: str):
            return {"message": f"Hello {name}"}

        @root_router.get("/redoc", include_in_schema=False)
        async def redoc_html():
            return get_redoc_html(
                openapi_url=app.openapi_url,
                title=app.title + " - ReDoc",
                redoc_js_url="/static/redoc/bundles/redoc.standalone.js",
            )

        app.include_router(root_router)
        app.include_router(api_router, prefix="/v3")

        return app
    except Exception as e:
        fail(e)


app_ = create_everest()


def main():
    uvicorn.run("everest.cmd.api:app_", reload=True)


if __name__ == "__main__":
    main()
