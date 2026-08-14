#!/usr/bin/env python3
"""Derive one GitHub-native project status from repository facts.

The module deliberately has no runtime dependencies outside Python's standard
library.  Its pure derivation functions are separately testable; GitHub writes
are limited to one fixed Issue and a small, namespaced label set.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass, field, replace
from typing import Any, Iterable


STATUS_MARKER = "<!-- agent-conversation:project-status:v1 -->"
META_ISSUE_MARKERS = (STATUS_MARKER, "<!-- agent-conversation:cross-repository-dashboard:")
META_ISSUE_LABELS = {"project-status", "portfolio-dashboard"}
STATUS_PREFIX = "workflow:"
STATUS_LABELS = {
    "Not started": ("workflow:not-started", "d4c5f9", "Open work not yet claimed by automation"),
    "Codex working": ("workflow:codex-working", "1d76db", "AI work or CI repair is in progress"),
    "Waiting for ChatGPT review": ("workflow:waiting-review", "fbca04", "Implementation is waiting for upstream review"),
    "Changes requested": ("workflow:changes-requested", "d93f0b", "Upstream requested changes that AI can address"),
    "Ready to merge": ("workflow:ready-to-merge", "0e8a16", "Review passed and checks succeeded"),
    "Blocked": ("workflow:blocked", "b60205", "Work is blocked"),
}
SPECIAL_LABELS = {
    "human-action-required": ("b60205", "A user decision or action is genuinely required"),
    "project-status": ("5319e7", "Fixed machine-generated project status Issue"),
}
SUCCESS_CONCLUSIONS = {"success", "neutral", "skipped"}
PROJECT_STATUS_CHECK_NAMES = {
    "project status",
    "update",  # Legacy job name before the workflow assigned a stable display name.
    "status / project status",
    "status / update",
}
PASS_MARKER = re.compile(r"chatgpt-upstream-review:head=([0-9a-f]+)\s+status=pass", re.I)
CHANGE_MARKER = re.compile(r"chatgpt-upstream-review:head=([0-9a-f]+)\s+status=changes-required", re.I)
CLAIM_MARKER = "<!-- codex-dispatch:claimed -->"
RELEASE_MARKER = "<!-- codex-dispatch:released -->"
BLOCK_MARKERS = ("<!-- codex-dispatch:blocked", "<!-- codex-followup:blocked")
START_MARKER = "<!-- codex-followup:started"
ADDRESSED_MARKER = "<!-- codex-followup:addressed"
LINK_RE = re.compile(r"(?i)\b(?:close[sd]?|fix(?:e[sd])?|resolve[sd]?|refs?)\s+#(\d+)")
DEPENDENCY_RE = re.compile(r"(?im)\b(?:blocked\s+by|depends\s+on)\s+(?:[^\n#]*?)#(\d+)")
HUMAN_BLOCK_RE = re.compile(
    r"(?i)\b(?:credentials?|permissions?|access grant|billing|payment|product decision|"
    r"research decision|user decision|human decision|manual approval|external approval)\b"
)
HUMAN_LABELS = {"human-action:decision", "human-action:credentials", "human-action:permission"}


@dataclass(frozen=True)
class Note:
    body: str
    created_at: str = ""
    note_id: str = ""
    commit_id: str = ""
    state: str = ""
    author_login: str = ""
    author_id: str = ""
    author_type: str = ""
    author_association: str = ""
    marker_trusted: bool = False


@dataclass(frozen=True)
class Check:
    name: str
    status: str
    conclusion: str = ""


@dataclass(frozen=True)
class WorkItem:
    kind: str
    number: int
    title: str
    url: str = ""
    state: str = "OPEN"
    body: str = ""
    labels: frozenset[str] = frozenset()
    comments: tuple[Note, ...] = ()
    reviews: tuple[Note, ...] = ()
    unresolved_threads: tuple[Note, ...] = ()
    checks: tuple[Check, ...] = ()
    draft: bool = False
    merged: bool = False
    head_sha: str = ""
    updated_at: str = ""
    linked_issues: tuple[int, ...] = ()
    dependencies: tuple[int, ...] = ()


@dataclass(frozen=True)
class Derived:
    item: WorkItem
    status: str
    detail: str
    human_action: str = ""


def _latest_marker(notes: Iterable[Note], needle: str) -> Note | None:
    matches = [note for note in notes if note.marker_trusted and needle in note.body.lower()]
    return max(matches, key=lambda note: (note.created_at, note.note_id), default=None)


def _latest_review_marker(notes: Iterable[Note], pattern: re.Pattern[str]) -> tuple[Note, str] | None:
    matches: list[tuple[Note, str]] = []
    for note in notes:
        if not note.marker_trusted:
            continue
        found = pattern.search(note.body)
        if found:
            matches.append((note, found.group(1).lower()))
    return max(matches, key=lambda pair: (pair[0].created_at, pair[0].note_id), default=None)


def _later(left: Note | None, right: Note | None) -> bool:
    if left is None:
        return False
    if right is None:
        return True
    return (left.created_at, left.note_id) > (right.created_at, right.note_id)


def _ci_state(checks: tuple[Check, ...]) -> str:
    if not checks:
        return "missing"
    if any(check.status.lower() != "completed" for check in checks):
        return "running"
    if any(check.conclusion.lower() not in SUCCESS_CONCLUSIONS for check in checks):
        return "failed"
    return "success"


def _is_project_status_check(name: str) -> bool:
    return name.strip().lower() in PROJECT_STATUS_CHECK_NAMES


def _is_meta_issue(body: str, labels: Iterable[str]) -> bool:
    return bool(META_ISSUE_LABELS.intersection(labels)) or any(marker in body for marker in META_ISSUE_MARKERS)


def _human_block(item: WorkItem, blocker: Note | None = None) -> bool:
    if item.labels.intersection(HUMAN_LABELS):
        return True
    return bool(blocker and HUMAN_BLOCK_RE.search(blocker.body))


def derive_pr(item: WorkItem) -> Derived:
    if item.merged:
        return Derived(item, "Completed", "Merged")
    if item.state.upper() != "OPEN":
        return Derived(item, "Completed", "Closed without merge")
    if item.labels.intersection(HUMAN_LABELS):
        return Derived(item, "Blocked", "Explicit human decision or access label", f"Resolve blocker on PR #{item.number}")

    all_notes = tuple(sorted(item.comments + item.reviews, key=lambda note: (note.created_at, note.note_id)))
    blocker = max(
        (
            note
            for note in all_notes
            if note.marker_trusted and any(marker in note.body.lower() for marker in BLOCK_MARKERS)
        ),
        key=lambda note: (note.created_at, note.note_id),
        default=None,
    )
    released = _latest_marker(all_notes, RELEASE_MARKER)
    if blocker and _later(blocker, released):
        human = _human_block(item, blocker)
        action = f"Resolve blocker on PR #{item.number}" if human else ""
        return Derived(item, "Blocked", "Explicit blocker reported", action)

    pass_signal = _latest_review_marker(all_notes, PASS_MARKER)
    change_signal = _latest_review_marker(all_notes, CHANGE_MARKER)
    approved = max(
        (note for note in item.reviews if note.state.upper() == "APPROVED"),
        key=lambda note: (note.created_at, note.note_id),
        default=None,
    )
    requested = max(
        (note for note in item.reviews if note.state.upper() == "CHANGES_REQUESTED"),
        key=lambda note: (note.created_at, note.note_id),
        default=None,
    )
    current_head = item.head_sha.lower()
    passed_current = bool(pass_signal and current_head.startswith(pass_signal[1]))
    if approved and (not approved.commit_id or approved.commit_id.lower() == current_head):
        passed_current = True

    changed_current = bool(change_signal and current_head.startswith(change_signal[1]))
    if requested and (not requested.commit_id or requested.commit_id.lower() == current_head):
        changed_current = True
    if item.unresolved_threads:
        changed_current = True

    latest_change_note = change_signal[0] if change_signal else requested
    started = _latest_marker(all_notes, START_MARKER)
    addressed = _latest_marker(all_notes, ADDRESSED_MARKER)
    ci = _ci_state(item.checks)

    if passed_current:
        if ci == "success":
            return Derived(item, "Ready to merge", "Review PASS and CI successful", f"Merge PR #{item.number}")
        if ci == "failed":
            return Derived(item, "Codex working", "Review passed; CI failed and can be repaired by AI")
        if ci == "running":
            return Derived(item, "Codex working", "Review passed; CI is running")
        return Derived(item, "Codex working", "Review passed; waiting for CI evidence")

    if changed_current:
        if _later(addressed, latest_change_note):
            return Derived(item, "Waiting for ChatGPT review", "Requested changes were addressed on a newer head")
        if _later(started, latest_change_note):
            return Derived(item, "Codex working", "Codex is addressing requested changes")
        return Derived(item, "Changes requested", "Upstream changes remain for AI to address")

    if ci == "failed":
        return Derived(item, "Codex working", "CI failed and can be repaired by AI")
    if ci == "running":
        return Derived(item, "Codex working", "CI is running")
    if change_signal and not current_head.startswith(change_signal[1]):
        return Derived(item, "Waiting for ChatGPT review", "A newer head is waiting for re-review")
    if item.draft:
        return Derived(item, "Waiting for ChatGPT review", "Draft PR is waiting for upstream review")
    return Derived(item, "Waiting for ChatGPT review", "Open PR is waiting for upstream review")


def derive_issue(item: WorkItem, open_issue_numbers: set[int]) -> Derived:
    if item.state.upper() != "OPEN":
        return Derived(item, "Completed", "Issue completed")
    if item.labels.intersection(HUMAN_LABELS):
        return Derived(item, "Blocked", "Explicit human decision or access label", f"Resolve blocker on Issue #{item.number}")
    notes = tuple(sorted(item.comments, key=lambda note: (note.created_at, note.note_id)))
    blocker = max(
        (
            note
            for note in notes
            if note.marker_trusted and any(marker in note.body.lower() for marker in BLOCK_MARKERS)
        ),
        key=lambda note: (note.created_at, note.note_id),
        default=None,
    )
    released = _latest_marker(notes, RELEASE_MARKER)
    if blocker and _later(blocker, released):
        human = _human_block(item, blocker)
        action = f"Resolve blocker on Issue #{item.number}" if human else ""
        return Derived(item, "Blocked", "Explicit blocker reported", action)
    open_dependencies = [number for number in item.dependencies if number in open_issue_numbers]
    if open_dependencies:
        refs = ", ".join(f"#{number}" for number in open_dependencies)
        return Derived(item, "Blocked", f"Blocked by {refs}")
    claimed = _latest_marker(notes, CLAIM_MARKER)
    if claimed and _later(claimed, released):
        return Derived(item, "Codex working", "Codex has claimed this Issue")
    return Derived(item, "Not started", "Open Issue has not been claimed")


def derive_all(items: Iterable[WorkItem]) -> list[Derived]:
    item_list = list(items)
    open_issues = {item.number for item in item_list if item.kind == "issue" and item.state.upper() == "OPEN"}
    derived_prs = {item.number: derive_pr(item) for item in item_list if item.kind == "pr"}
    result: list[Derived] = []
    for item in item_list:
        if item.kind == "pr":
            result.append(derived_prs[item.number])
            continue
        linked = [derived_prs[number] for number in item.linked_issues if number in derived_prs]
        if linked:
            source = linked[0]
            result.append(Derived(item, source.status, f"Tracked by PR #{source.item.number}: {source.detail}"))
        else:
            result.append(derive_issue(item, open_issues))
    return result


def render_status(repository: str, derived: Iterable[Derived], completed: Iterable[WorkItem] = ()) -> str:
    # A linked Issue mirrors its PR for label readability, but the fixed status
    # Issue shows the PR only so merge actions and work items are not duplicated.
    rows = [row for row in derived if not (row.item.kind == "issue" and row.item.linked_issues)]
    human = [row for row in rows if row.human_action]
    in_progress = [row for row in rows if row.status == "Codex working"]
    waiting = [row for row in rows if row.status in {"Not started", "Waiting for ChatGPT review", "Changes requested"}]
    blocked = [row for row in rows if row.status == "Blocked"]
    ready = [row for row in rows if row.status == "Ready to merge"]

    def line(row: Derived) -> str:
        kind = "PR" if row.item.kind == "pr" else "Issue"
        label = f"[{kind} #{row.item.number}: {row.item.title}]({row.item.url})" if row.item.url else f"{kind} #{row.item.number}: {row.item.title}"
        return f"- **{row.status}** — {label} — {row.detail}"

    def section(title: str, values: list[Derived], empty: str = "_None._") -> list[str]:
        return [f"## {title}", "", *(line(row) for row in values)] if values else [f"## {title}", "", empty]

    body = [
        STATUS_MARKER,
        "# Project status",
        "",
        f"> Machine-generated from GitHub facts in `{repository}`. Do not edit this body by hand.",
        "",
        "## Human action required",
        "",
    ]
    if human:
        body.extend(
            f"- **{row.human_action}** — [{row.item.kind.upper()} #{row.item.number}]({row.item.url}) — {row.detail}"
            for row in human
        )
    else:
        body.append("_None. It is safe for the user to do nothing._")
    body.extend([""] + section("Ready to merge", ready) + [""])
    body.extend(section("AI working", in_progress) + [""])
    body.extend(section("Waiting", waiting) + [""])
    body.extend(section("Blocked", blocked) + [""])
    completed_rows = list(completed)
    body.extend(["## Recently completed", ""])
    if completed_rows:
        for item in completed_rows:
            kind = "PR" if item.kind == "pr" else "Issue"
            label = f"[{kind} #{item.number}: {item.title}]({item.url})" if item.url else f"{kind} #{item.number}: {item.title}"
            body.append(f"- ✅ {label}")
    else:
        body.append("_None._")
    body.extend(
        [
            "",
            "---",
            "",
            "`Ready to merge` requires a current-head PASS/approval plus successful CI. CI failures, review cycles, and normal AI handoffs never create a human action. Dependency blocks only become human actions when an explicit credential, permission, product, research, or approval blocker is recorded.",
        ]
    )
    return "\n".join(body).rstrip() + "\n"


class GitHubClient:
    def __init__(
        self,
        repository: str,
        token: str,
        api_url: str = "https://api.github.com",
        trusted_marker_actors: Iterable[str] = (),
    ) -> None:
        if repository.count("/") != 1:
            raise ValueError("repository must be in owner/name form")
        self.repository = repository
        self.token = token
        self.api_url = api_url.rstrip("/")
        self.trusted_marker_actors = frozenset(
            actor.strip().lower() for actor in trusted_marker_actors if actor.strip()
        )

    def request(self, method: str, path: str, payload: Any | None = None, *, accept: str = "application/vnd.github+json") -> Any:
        url = path if path.startswith("http") else f"{self.api_url}{path}"
        data = None if payload is None else json.dumps(payload).encode("utf-8")
        request = urllib.request.Request(
            url,
            data=data,
            method=method,
            headers={
                "Accept": accept,
                "Authorization": f"Bearer {self.token}",
                "X-GitHub-Api-Version": os.getenv("GITHUB_API_VERSION", "2026-03-10"),
                "User-Agent": "agent-conversation-project-status",
                "Content-Type": "application/json",
                "Cache-Control": "no-cache",
            },
        )
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                raw = response.read()
                return json.loads(raw) if raw else None
        except urllib.error.HTTPError as exc:
            detail = exc.read().decode("utf-8", errors="replace")
            raise RuntimeError(f"GitHub API {method} {path} failed ({exc.code}): {detail}") from exc

    def paginate(self, path: str) -> list[dict[str, Any]]:
        separator = "&" if "?" in path else "?"
        page = 1
        result: list[dict[str, Any]] = []
        while True:
            batch = self.request("GET", f"{path}{separator}per_page=100&page={page}")
            if not isinstance(batch, list):
                raise RuntimeError(f"Expected a list from GitHub API path {path}")
            result.extend(batch)
            if len(batch) < 100:
                return result
            page += 1

    def _notes(self, values: Iterable[dict[str, Any]]) -> tuple[Note, ...]:
        notes: list[Note] = []
        for value in values:
            author = value.get("user") or value.get("author") or {}
            login = str(author.get("login") or "")
            author_id = str(author.get("id") or "")
            trusted = login.lower() in self.trusted_marker_actors
            if author_id:
                trusted = trusted or f"id:{author_id}".lower() in self.trusted_marker_actors
            notes.append(
                Note(
                    body=value.get("body") or "",
                    created_at=value.get("submitted_at") or value.get("created_at") or "",
                    note_id=str(value.get("id") or ""),
                    commit_id=value.get("commit_id") or "",
                    state=value.get("state") or "",
                    author_login=login,
                    author_id=author_id,
                    author_type=str(author.get("type") or ""),
                    author_association=str(value.get("author_association") or ""),
                    marker_trusted=trusted,
                )
            )
        return tuple(notes)

    def _unresolved_threads(self, number: int) -> tuple[Note, ...]:
        owner, name = self.repository.split("/", 1)
        query = """query($owner:String!,$name:String!,$number:Int!){repository(owner:$owner,name:$name){pullRequest(number:$number){reviewThreads(first:100){nodes{isResolved comments(first:20){nodes{id body createdAt}}}}}}}"""
        try:
            data = self.request("POST", "/graphql", {"query": query, "variables": {"owner": owner, "name": name, "number": number}})
            nodes = data["data"]["repository"]["pullRequest"]["reviewThreads"]["nodes"]
            return tuple(
                Note(body=comment.get("body") or "", created_at=comment.get("createdAt") or "", note_id=str(comment.get("id") or ""))
                for node in nodes
                if not node.get("isResolved")
                for comment in node.get("comments", {}).get("nodes", [])[-1:]
            )
        except (KeyError, TypeError) as exc:
            raise RuntimeError(f"Could not read review threads for PR #{number}") from exc

    def load(self) -> tuple[list[WorkItem], list[WorkItem], list[dict[str, Any]]]:
        base = f"/repos/{self.repository}"
        raw_issues = self.paginate(f"{base}/issues?state=open")
        raw_prs = self.paginate(f"{base}/pulls?state=open")
        completed_prs = self.paginate(f"{base}/pulls?state=closed&sort=updated&direction=desc")[:20]
        items: list[WorkItem] = []
        issue_records = [value for value in raw_issues if "pull_request" not in value]
        for value in issue_records:
            labels = frozenset(label["name"] for label in value.get("labels", []))
            if _is_meta_issue(value.get("body") or "", labels):
                continue
            comments = self._notes(self.paginate(f"{base}/issues/{value['number']}/comments"))
            dependencies = set(int(number) for number in DEPENDENCY_RE.findall(value.get("body") or ""))
            for note in comments:
                if not note.marker_trusted:
                    continue
                dependencies.update(int(number) for number in DEPENDENCY_RE.findall(note.body))
            native_dependencies = self.paginate(f"{base}/issues/{value['number']}/dependencies/blocked_by")
            dependencies.update(int(dependency["number"]) for dependency in native_dependencies)
            items.append(
                WorkItem(
                    kind="issue",
                    number=value["number"],
                    title=value["title"],
                    url=value["html_url"],
                    body=value.get("body") or "",
                    labels=labels,
                    comments=comments,
                    dependencies=tuple(sorted(dependencies)),
                    updated_at=value.get("updated_at") or "",
                )
            )

        pr_numbers: set[int] = set()
        for value in raw_prs:
            number = value["number"]
            pr_numbers.add(number)
            issue_comments = self.paginate(f"{base}/issues/{number}/comments")
            reviews = self.paginate(f"{base}/pulls/{number}/reviews")
            check_data = self.request("GET", f"{base}/commits/{value['head']['sha']}/check-runs")
            checks = tuple(
                Check(run.get("name") or "check", run.get("status") or "", run.get("conclusion") or "")
                for run in check_data.get("check_runs", [])
                if not _is_project_status_check(run.get("name") or "")
            )
            body = value.get("body") or ""
            linked_issues = tuple(sorted({int(number) for number in LINK_RE.findall(body)}))
            items.append(
                WorkItem(
                    kind="pr",
                    number=number,
                    title=value["title"],
                    url=value["html_url"],
                    body=body,
                    labels=frozenset(label["name"] for label in value.get("labels", [])),
                    comments=self._notes(issue_comments),
                    reviews=self._notes(reviews),
                    unresolved_threads=self._unresolved_threads(number),
                    checks=checks,
                    draft=bool(value.get("draft")),
                    head_sha=value["head"]["sha"],
                    updated_at=value.get("updated_at") or "",
                    linked_issues=linked_issues,
                )
            )

        # Attach open PR numbers to the Issues they close/reference.
        issue_to_prs: dict[int, list[int]] = {}
        for item in items:
            if item.kind == "pr":
                for issue_number in item.linked_issues:
                    issue_to_prs.setdefault(issue_number, []).append(item.number)
        items = [
            replace(item, linked_issues=tuple(issue_to_prs.get(item.number, ()))) if item.kind == "issue" else item
            for item in items
        ]

        completed = [
            WorkItem(
                kind="pr",
                number=value["number"],
                title=value["title"],
                url=value["html_url"],
                state="CLOSED",
                merged=bool(value.get("merged_at")),
                updated_at=value.get("updated_at") or "",
            )
            for value in completed_prs
            if value.get("merged_at")
        ][:5]
        status_records = [
            issue
            for issue in issue_records
            if "project-status" in {label["name"] for label in issue.get("labels", [])}
            or STATUS_MARKER in (issue.get("body") or "")
        ]
        if not status_records:
            status_records = [
                issue
                for issue in self.paginate(f"{base}/issues?state=all&labels=project-status&sort=updated&direction=desc")
                if "pull_request" not in issue
            ][:1]
        return items, completed, status_records

    def _ensure_labels(self, include_workflow: bool) -> None:
        base = f"/repos/{self.repository}"
        existing = {label["name"] for label in self.paginate(f"{base}/labels")}
        definitions = {"project-status": SPECIAL_LABELS["project-status"]}
        if include_workflow:
            definitions.update({name: (color, description) for name, color, description in STATUS_LABELS.values()})
            definitions["human-action-required"] = SPECIAL_LABELS["human-action-required"]
        for name, (color, description) in definitions.items():
            if name not in existing:
                self.request("POST", f"{base}/labels", {"name": name, "color": color, "description": description})

    def publish(self, body: str, derived: list[Derived], status_records: list[dict[str, Any]], title: str, apply_labels: bool) -> tuple[str, bool]:
        base = f"/repos/{self.repository}"
        self._ensure_labels(include_workflow=apply_labels)
        if apply_labels:
            derived_by_key = {(row.item.kind, row.item.number): row for row in derived}
            for row in derived_by_key.values():
                label = STATUS_LABELS.get(row.status, (None, "", ""))[0]
                if not label:
                    continue
                preserved = sorted(name for name in row.item.labels if not name.startswith(STATUS_PREFIX) and name != "human-action-required")
                desired = preserved + [label]
                if row.human_action:
                    desired.append("human-action-required")
                if set(desired) != set(row.item.labels):
                    self.request("PUT", f"{base}/issues/{row.item.number}/labels", {"labels": desired})

        # Use a label-targeted fresh read in addition to the initial snapshot.
        # GitHub's broad Issue list can lag immediately after creation; selecting
        # the oldest match also makes concurrent first runs converge on one Issue.
        targeted = self.paginate(f"{base}/issues?state=all&labels=project-status&sort=created&direction=asc")
        candidates: dict[int, dict[str, Any]] = {}
        for issue in status_records + targeted:
            if "pull_request" in issue:
                continue
            if "project-status" in {label["name"] for label in issue.get("labels", [])} or STATUS_MARKER in (issue.get("body") or ""):
                candidates[int(issue["number"])] = issue
        ordered = [candidates[number] for number in sorted(candidates)]
        status_issue = ordered[0] if ordered else None
        if status_issue is None:
            created = self.request("POST", f"{base}/issues", {"title": title, "body": body, "labels": ["project-status"]})
            node_id = created.get("node_id")
            if node_id:
                mutation = "mutation($issueId:ID!){pinIssue(input:{issueId:$issueId}){issue{id}}}"
                try:
                    self.request("POST", "/graphql", {"query": mutation, "variables": {"issueId": node_id}})
                except RuntimeError as exc:
                    # Pinning is a discoverability enhancement. A full pin set
                    # must not prevent the canonical status Issue from existing.
                    print(f"Warning: status Issue was created but could not be pinned: {exc}", file=sys.stderr)
            return created["html_url"], True
        for duplicate in ordered[1:]:
            if duplicate.get("state") == "open":
                duplicate_labels = sorted(
                    label["name"] for label in duplicate.get("labels", []) if label["name"] != "project-status"
                )
                self.request(
                    "PATCH",
                    f"{base}/issues/{duplicate['number']}",
                    {"state": "closed", "state_reason": "not_planned", "labels": duplicate_labels},
                )
            duplicate_node_id = duplicate.get("node_id")
            if duplicate_node_id:
                mutation = "mutation($issueId:ID!){unpinIssue(input:{issueId:$issueId}){issue{id}}}"
                try:
                    self.request("POST", "/graphql", {"query": mutation, "variables": {"issueId": duplicate_node_id}})
                except RuntimeError:
                    # The duplicate may already be unpinned; convergence of the
                    # canonical body remains the required operation.
                    pass
        existing_labels = {label["name"] for label in status_issue.get("labels", [])}
        changed = (
            status_issue.get("title") != title
            or status_issue.get("body") != body
            or status_issue.get("state") != "open"
            or "project-status" not in existing_labels
        )
        if changed:
            labels = sorted((existing_labels - {"human-action-required"}) | {"project-status"})
            updated = self.request(
                "PATCH",
                f"{base}/issues/{status_issue['number']}",
                {"title": title, "body": body, "state": "open", "labels": labels},
            )
            return updated["html_url"], True
        return status_issue["html_url"], False


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", default=os.getenv("GITHUB_REPOSITORY", ""), help="GitHub repository in owner/name form")
    parser.add_argument("--status-title", default="Project status")
    parser.add_argument("--dry-run", action="store_true", help="Print the derived Issue body without writing")
    parser.add_argument("--no-labels", action="store_true", help="Do not synchronize workflow status labels")
    parser.add_argument(
        "--trusted-marker-actors",
        default=os.getenv("STATUS_TRUSTED_MARKER_ACTORS", ""),
        help="Comma-separated exact GitHub logins or id:<numeric-id> selectors allowed to emit control markers",
    )
    parser.add_argument("--api-url", default=os.getenv("GITHUB_API_URL", "https://api.github.com"))
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    args = parse_args(argv)
    if not args.repo:
        print("--repo or GITHUB_REPOSITORY is required", file=sys.stderr)
        return 2
    token = os.getenv("GITHUB_TOKEN") or os.getenv("GH_TOKEN")
    if not token:
        print("GITHUB_TOKEN or GH_TOKEN is required", file=sys.stderr)
        return 2
    trusted_marker_actors = [actor for actor in args.trusted_marker_actors.split(",") if actor.strip()]
    client = GitHubClient(args.repo, token, args.api_url, trusted_marker_actors)
    items, completed, status_records = client.load()
    derived = derive_all(items)
    body = render_status(args.repo, derived, completed)
    if args.dry_run:
        print(body, end="")
        return 0
    url, changed = client.publish(body, derived, status_records, args.status_title, not args.no_labels)
    print(f"Project status {'updated' if changed else 'unchanged'}: {url}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
