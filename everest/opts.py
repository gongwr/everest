# Copyright (c) 2023 WenRui Gong
# All rights reserved.


__all__ = [
    'list_api_opts',
    'list_manage_opts',
]

import copy
import itertools

from osprofiler import opts as profiler

import everest.common.config
import everest.common.wsgi


_api_opts = [
    (None, list(itertools.chain(
        everest.common.config.common_opts,
        everest.common.wsgi.bind_opts,
        everest.common.wsgi.eventlet_opts,
        everest.common.wsgi.socket_opts,
        everest.common.wsgi.store_opts,
        everest.common.wsgi.cli_opts))),
    ('task', everest.common.config.task_opts),
    profiler.list_opts()[0],
    ('wsgi', everest.common.config.wsgi_opts),
]
_manage_opts = [
    (None, [])
]


def list_api_opts():
    """Return a list of oslo_config options available in Everest API service.

    Each element of the list is a tuple. The first element is the name of the
    group under which the list of elements in the second element will be
    registered. A group name of None corresponds to the [DEFAULT] group in
    config files.

    This function is also discoverable via the 'everest.api' entry point
    under the 'oslo_config.opts' namespace.

    The purpose of this is to allow tools like the Oslo sample config file
    generator to discover the options exposed to users by Everest.

    :returns: a list of (group_name, opts) tuples
    """

    return [(g, copy.deepcopy(o)) for g, o in _api_opts]


def list_manage_opts():
    """Return a list of oslo_config options available in Everest manage."""
    return [(g, copy.deepcopy(o)) for g, o in _manage_opts]

