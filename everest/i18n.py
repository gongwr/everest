# Copyright 2014 Red Hat, Inc.
# All Rights Reserved.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.

import oslo_i18n as i18n

DOMAIN = 'everest'

_translators = i18n.TranslatorFactory(domain=DOMAIN)

# The primary translation function using the well-known name "_"
_ = _translators.primary


def enable_lazy(enable=True):
    return i18n.enable_lazy(enable)


def translate(value, user_locale=None):
    return i18n.translate(value, user_locale)


def get_available_languages(domain=DOMAIN):
    return i18n.get_available_languages(domain)
