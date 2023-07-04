# Copyright (c) 2023 WenRui Gong
# All rights reserved.

from fastapi import APIRouter

from everest.api.api_v1.endpoints import user
from everest.api.api_v1.endpoints import project

api_router = APIRouter()
api_router.include_router(user.router, prefix="/users", tags=["users"])
api_router.include_router(project.router, prefix="/projects", tags=["projects"])
