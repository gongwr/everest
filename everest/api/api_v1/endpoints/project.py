# Copyright (c) 2023 WenRui Gong
# All rights reserved.


import http.client

from fastapi import APIRouter

router = APIRouter()


def _list_projects():
    return [
        {"project_id": 1},
        {"project_id": 2},
        {"project_id": 3},
    ]


def _get_project(project_id: int):
    return {"project_id": project_id}


@router.get("")
async def get_projects():
    """List projects.

    GET/HEAD /v3/projects
    """
    return _list_projects()


@router.head("")
async def list_projects():
    """List projects.

    GET/HEAD /v3/projects
    """
    return _list_projects()


@router.get("/{project_id}")
async def get_project(project_id: int):
    """Get project by project id.

    GET/HEAD /v3/projects/{project_id}
    """
    return _get_project(project_id)


@router.head("/{project_id}")
async def list_project(project_id: int):
    """Get project by project id.

    GET/HEAD /v3/projects/{project_id}
    """
    return _get_project(project_id)


@router.post("")
async def create_project():
    """Create project.

    POST /v3/projects
    """
    return http.client.CREATED


@router.patch("/{project_id}")
async def update_project(project_id: int):
    """Update project.

    PATCH /v3/projects/{project_id}
    """
    return _get_project(project_id)


@router.delete("/{project_id}")
async def delete_project(project_id: int):
    """Delete project.

    DELETE /v3/projects/{project_id}
    """
    return http.client.NO_CONTENT


@router.get("/{project_id}/tags")
async def get_project_tags(project_id: int):
    """List project tags.

    GET /v3/projects/{project_id}/tags
    """
    return [
        {"tag_id": 1},
        {"tag_id": 2},
        {"tag_id": 3},
    ]


@router.put("/{project_id}/tags")
async def update_project_tags(project_id: int):
    """Update all tags associated with a given project.

    PUT /v3/projects/{project_id}/tags
    """
    return http.client.NO_CONTENT


@router.delete("/{project_id}/tags")
async def delete_project_tags(project_id: int):
    """Delete all tags associated with a given project.

    DELETE /v3/projects/{project_id}/tags
    """
    return http.client.NO_CONTENT


@router.get("/{project_id}/tags/{value}")
async def get_project_tag(project_id: int, value: str):
    """Get information for a single tag associated with a given project.

    GET /v3/projects/{project_id}/tags/{value}
    """
    return None, http.client.NO_CONTENT


@router.put("/{project_id}/tags/{value}")
async def add_project_tag(project_id: int, value: str):
    """Add a single tag to a project.

    PUT /v3/projects/{project_id}/tags/{value}
    """
    return http.client.NO_CONTENT


@router.delete("/{project_id}/tags/{value}")
async def delete_project_tag(project_id: int, value: str):
    """Delete a single tag from a project.

    /v3/projects/{project_id}/tags/{value}
    """
    return http.client.NO_CONTENT


def _check_project_user_grants(project_id: int, user_id: int):
    return {
        "project_id": project_id,
        "user_id": user_id,
    }


@router.get("/{project_id}/users/{user_id}")
async def get_project_group_user(project_id: int, user_id: int):
    """List grants for user on project.

    GET/HEAD /v3/projects/{project_id}/users/{user_id}
    """
    return _check_project_user_grants(project_id, user_id)


@router.head("/{project_id}/users/{user_id}")
async def list_project_group_user(project_id: int, user_id: int):
    """List grants for user on project.

    GET/HEAD /v3/projects/{project_id}/users/{user_id}
    """
    return _check_project_user_grants(project_id, user_id)


def _get_project_user_role(project_id: int, user_id: int, role_id: int):
    return {
        "project_id": project_id,
        "user_id": user_id,
        "role_id": role_id,
    }


@router.get("/{project_id}/users/{user_id}/roles/{role_id}")
async def get_project_user_role(project_id: int, user_id: int, role_id: int):
    """Check grant for project, user, role.

    GET/HEAD /v3/projects/{project_id/users/{user_id}/roles/{role_id}
    """
    return _get_project_user_role(project_id, user_id, role_id)


@router.head("/{project_id}/users/{user_id}/roles/{role_id}")
async def list_project_user_role(project_id: int, user_id: int, role_id: int):
    """Check grant for project, user, role.

    GET/HEAD /v3/projects/{project_id/users/{user_id}/roles/{role_id}
    """
    return _get_project_user_role(project_id, user_id, role_id)


@router.put("/{project_id}/users/{user_id}/roles/{role_id}")
async def grant_project_user_role(project_id: int, user_id: int, role_id: int):
    """Grant role for user on project.

    PUT /v3/projects/{project_id}/users/{user_id}/roles/{role_id}
    """
    return http.client.NO_CONTENT


@router.delete("/{project_id}/users/{user_id}/roles/{role_id}")
async def revoke_project_user_role(project_id: int, user_id: int, role_id: int):
    """Delete grant of role for user on project.

    DELETE /v3/projects/{project_id}/users/{user_id}/roles/{role_id}
    """
    return http.client.NO_CONTENT


def _check_project_group_role_grants(project_id: int, group_id: int, role_id: int):
    return {
        "project_id": project_id,
        "group_id": group_id,
        "role_id": role_id,
    }


@router.get("/{project_id}/groups/{group_id}/roles/{role_id}")
async def get_project_group_role(project_id: int, group_id: int, role_id: int):
    """Check grant for project, group, role.

    GET/HEAD /v3/projects/{project_id/groups/{group_id}/roles/{role_id}
    """
    return _check_project_group_role_grants(project_id, group_id, role_id)


@router.head("/{project_id}/groups/{group_id}/roles/{role_id}")
async def list_project_group_role(project_id: int, group_id: int, role_id: int):
    """Check grant for project, group, role.

    GET/HEAD /v3/projects/{project_id/groups/{group_id}/roles/{role_id}
    """
    return _check_project_group_role_grants(project_id, group_id, role_id)


@router.put("/{project_id}/groups/{group_id}/roles/{role_id}")
async def grant_project_group_role(project_id: int, group_id: int, role_id: int):
    """Grant role for group on project.

    PUT /v3/projects/{project_id}/groups/{group_id}/roles/{role_id}
    """
    return http.client.NO_CONTENT


@router.delete("/{project_id}/groups/{group_id}/roles/{role_id}")
async def revoke_project_group_role(project_id: int, group_id: int, role_id: int):
    """Delete grant of role for group on project.

    DELETE /v3/projects/{project_id}/groups/{group_id}/roles/{role_id}
    """
    return http.client.NO_CONTENT


def _check_project_group_grants(project_id: int, group_id: int):
    return {
        "project_id": project_id,
        "group_id": group_id,
    }


@router.get("/{project_id}/groups/{group_id}")
async def get_project_group(project_id: int, group_id: int):
    """List grants for group on project.

    GET/HEAD /v3/projects/{project_id}/groups/{group_id}
    """
    return _check_project_group_grants(project_id, group_id)


@router.head("/{project_id}/groups/{group_id}")
async def list_project_group(project_id: int, group_id: int):
    """List grants for group on project.

    GET/HEAD /v3/projects/{project_id}/groups/{group_id}
    """
    return _check_project_group_grants(project_id, group_id)


