# Copyright (c) 2023 WenRui Gong
# All rights reserved.


from alembic import op
from oslo_config import cfg
from oslo_log import log as logging
from sqlalchemy import Boolean, Integer, String, Text
from sqlalchemy import Column
from sqlalchemy import ForeignKey

LOG = logging.getLogger(__name__)
CONF = cfg.CONF

# FIXME(stephenfin): Remove this as soon as we're done reworking the
# migrations. Until then, this is necessary to allow us to use the native
# alembic tooling (which won't register opts). Alternatively, maybe
# the server default *shouldn't* rely on a (changeable) config option value?
try:
    service_provider_relay_state_prefix_default = CONF.saml.relay_state_prefix
except Exception:
    service_provider_relay_state_prefix_default = 'ss:mem:'


def _add_identity_provider_table():
    op.create_table(
        'identity_provider',
        Column('id', String(length=64), primary_key=True),
        Column('enabled', Boolean, nullable=False),
        Column('description', Text(), nullable=True),
        Column('domain_id', String(length=64), nullable=False),
        Column('authorization_ttl', Integer, nullable=True),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_idp_remote_ids_table():
    op.create_table(
        'idp_remote_ids',
        Column('idp_id', String(length=64), ForeignKey('identity_provider.id', ondelete='CASCADE')),
        Column('remote_id', String(length=255), primary_key=True),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_mapping_table():
    op.create_table(
        'mapping',
        Column('id', String(length=64), primary_key=True),
        Column('rules', Text(), nullable=False),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_federation_protocol_table():
    op.create_table(
        'federation_protocol',
        Column('id', String(length=64), primary_key=True),
        Column('idp_id', String(length=64), ForeignKey('identity_provider.id', ondelete='CASCADE'), primary_key=True),
        Column('mapping_id', String(length=64), nullable=False),
        Column('remote_id_attribute', String(length=64)),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def _add_service_provider_table():
    op.create_table(
        'service_provider',
        Column('auth_url', String(length=256), nullable=False),
        Column('id', String(length=64), primary_key=True),
        Column('enabled', Boolean(), nullable=False),
        Column('description', Text(), nullable=True),
        Column('sp_url', String(length=256), nullable=False),
        Column('relay_state_prefix', String(length=256), nullable=False,
               server_default=service_provider_relay_state_prefix_default),
        mysql_engine='InnoDB',
        mysql_charset='utf8',
    )


def upgrade():
    _add_identity_provider_table()
    _add_idp_remote_ids_table()
    _add_mapping_table()
    _add_federation_protocol_table()
    _add_service_provider_table()
