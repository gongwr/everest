# Copyright 2010 United States Government as represented by the
# Administrator of the National Aeronautics and Space Administration.
# All Rights Reserved.
#
# Copyright 2013 OpenStack Foundation
# Copyright 2013 IBM Corp.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

"""Database setup and migration commands."""

from oslo_config import cfg
from oslo_db import options as db_options


db_options.set_defaults(cfg.CONF)


# Migration-related constants
EXPAND_BRANCH = 'expand'
CONTRACT_BRANCH = 'contract'
CURRENT_RELEASE = 'bravo'
ALEMBIC_INIT_VERSION = 'alpha'
