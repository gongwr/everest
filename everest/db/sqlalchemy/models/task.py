# Copyright (c) 2023 WenRui Gong
# All rights reserved.

import uuid

from oslo_db.sqlalchemy import models
from sqlalchemy import Column, DateTime, ForeignKey, Index, String, Text
from sqlalchemy.orm import backref, relationship

from everest.db.sqlalchemy.models.base import ModelBase, EverestBase, JSONEncodedDict


class Task(ModelBase, EverestBase):
    """Represents a task in the datastore"""
    __tablename__ = 'tasks'
    __table_args__ = (Index('ix_tasks_type', 'type'),
                      Index('ix_tasks_status', 'status'),
                      Index('ix_tasks_owner', 'owner'),
                      Index('ix_tasks_deleted', 'deleted'),
                      Index('ix_tasks_updated_at', 'updated_at'))

    id = Column(String(36), primary_key=True,
                default=lambda: str(uuid.uuid4()))
    type = Column(String(30), nullable=False)
    status = Column(String(30), nullable=False)
    owner = Column(String(255), nullable=False)
    expires_at = Column(DateTime, nullable=True)
    request_id = Column(String(64), nullable=True)
    user_id = Column(String(64), nullable=True)


class TaskInfo(ModelBase, models.ModelBase):
    """Represents task info in the datastore"""
    __tablename__ = 'task_info'

    task_id = Column(String(36),
                     ForeignKey('tasks.id'),
                     primary_key=True,
                     nullable=False)

    task = relationship(Task, backref=backref('info', uselist=False))

    # NOTE(nikhil): input and result are stored as text in the DB.
    # SQLAlchemy marshals the data to/from JSON using custom type
    # JSONEncodedDict. It uses simplejson underneath.
    input = Column(JSONEncodedDict())
    result = Column(JSONEncodedDict())
    message = Column(Text)
