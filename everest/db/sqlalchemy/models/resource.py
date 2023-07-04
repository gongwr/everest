# Copyright (c) 2014 Hewlett-Packard Development Company, L.P.
# Copyright (c) 2023 WenRui Gong
# All rights reserved.


from sqlalchemy import Column
from sqlalchemy import Boolean, String, Text, Unicode
from sqlalchemy import ForeignKey, UniqueConstraint
from sqlalchemy.orm import collections, relationship

from everest.common import resource_options
from everest.db.sqlalchemy.models.base import ModelBase
from everest.db.sqlalchemy.models.base import ModelDictMixin, ModelDictMixinWithExtras
from everest.db.sqlalchemy.models.base import JSONEncodedDict
from everest.common.resource_options import project_resource_options as pro

NULL_DOMAIN_ID = '<<null>>'


class Project(ModelBase, ModelDictMixinWithExtras):
    # NOTE(henry-nash): From the manager and above perspective, the domain_id
    # is nullable.  However, to ensure uniqueness in multiprocess
    # configurations, it is better to still use the sql uniqueness constraint.
    # Since the support for a nullable component of a uniqueness constraint
    # across different sql databases is mixed, we instead store a special value
    # to represent null, as defined in NULL_DOMAIN_ID above.

    def to_dict(self, include_extra_dict=False):
        d = super(Project, self).to_dict(
            include_extra_dict=include_extra_dict)
        if d['domain_id'] == NULL_DOMAIN_ID:
            d['domain_id'] = None
        # NOTE(notmorgan): Eventually it may make sense to drop the empty
        # option dict creation to the superclass (if enough models use it)
        d['options'] = resource_options.ref_mapper_to_dict_options(self)
        return d

    @classmethod
    def from_dict(cls, project_dict):
        new_dict = project_dict.copy()
        # TODO(morgan): move this functionality to a common location
        ros = {}
        options = new_dict.pop('options', {})
        for opt in cls.resource_options_registry.options:
            if opt.option_name in options:
                opt_value = options[opt.option_name]
                # NOTE(notmorgan): None is always a valid type
                if opt_value is not None:
                    opt.validator(opt_value)
                ros[opt.option_id] = opt_value
        project_obj = super(Project, cls).from_dict(new_dict)
        setattr(project_obj, '_resource_options', ros)
        return project_obj

    __tablename__ = 'project'
    attributes = ['id', 'name', 'domain_id', 'description', 'enabled',
                  'parent_id', 'is_domain', 'tags']
    resource_options_registry = pro.PROJECT_OPTIONS_REGISTRY
    id = Column(String(64), primary_key=True)
    name = Column(String(64), nullable=False)
    domain_id = Column(String(64), ForeignKey('project.id'),
                       nullable=False)
    description = Column(Text())
    enabled = Column(Boolean)
    extra = Column(JSONEncodedDict, default={}, nullable=False)
    parent_id = Column(String(64), ForeignKey('project.id'))
    is_domain = Column(Boolean, default=False, nullable=False,
                       server_default='0')
    _tags = relationship(
        'ProjectTag',
        single_parent=True,
        lazy='subquery',
        cascade='all,delete-orphan',
        backref='project',
        primaryjoin='and_(ProjectTag.project_id==Project.id)'
    )
    _resource_option_mapper = relationship(
        'ProjectOption',
        single_parent=True,
        cascade='all,delete,delete-orphan',
        lazy='subquery',
        backref='project',
        collection_class=collections.attribute_mapped_collection('option_id')
    )

    # Unique constraint across two columns to create the separation
    # rather than just only 'name' being unique
    __table_args__ = (UniqueConstraint('domain_id', 'name'),)

    @property
    def tags(self):
        if self._tags:
            return [tag.name for tag in self._tags]
        return []

    @tags.setter
    def tags(self, values):
        new_tags = []
        for tag in values:
            tag_ref = ProjectTag()
            tag_ref.project_id = self.id
            tag_ref.name = str(tag)
            new_tags.append(tag_ref)
        self._tags = new_tags


class ProjectTag(ModelBase, ModelDictMixin):

    def to_dict(self):
        d = super(ProjectTag, self).to_dict()
        return d

    __tablename__ = 'project_tag'
    attributes = ['project_id', 'name']
    project_id = Column(
        String(64), ForeignKey('project.id', ondelete='CASCADE'),
        nullable=False, primary_key=True)
    name = Column(Unicode(255), nullable=False, primary_key=True)
    __table_args__ = (UniqueConstraint('project_id', 'name'),)


class ProjectOption(ModelBase):
    __tablename__ = 'project_option'
    project_id = Column(String(64),
                        ForeignKey('project.id', ondelete='CASCADE'),
                        nullable=False, primary_key=True)
    option_id = Column(String(4), nullable=False,
                       primary_key=True)
    option_value = Column(JSONEncodedDict, default={}, nullable=False)

    def __init__(self, option_id, option_value, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.option_id = option_id
        self.option_value = option_value
