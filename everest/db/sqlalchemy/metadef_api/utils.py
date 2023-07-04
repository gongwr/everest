# Copyright (c) 2014 Hewlett-Packard Development Company, L.P.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.


def drop_protected_attrs(model_class, values):
    """
    Removed protected attributes from values dictionary using the models
    __protected_attributes__ field.
    """
    for attr in model_class.__protected_attributes__:
        if attr in values:
            del values[attr]
