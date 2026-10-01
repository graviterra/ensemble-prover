"""Bounded opt-in mathematical memory configuration."""

from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
import math
import os
from pathlib import Path
from .model import integer, text


class MemoryMode(str, Enum):
    OFF = "off"
    OBSERVE = "observe"
    ASSIST = "assist"
    DEVELOP = "develop"


@dataclass(frozen=True)
class MemoryConfig:
    mode: str = "off"
    root: str = ""
    theory_mode: str = "off"
    cheap_candidate_cap: int = 64
    prepared_candidate_cap: int = 8
    probe_cap: int = 4
    outbox_event_cap: int = 256
    outbox_byte_cap: int = 16 * 1024 * 1024
    artifact_byte_cap: int = 16 * 1024 * 1024
    artifact_store_byte_cap: int = 512 * 1024 * 1024
    artifact_count_cap: int = 65536
    query_scan_cap: int = 4096
    event_count_cap: int = 65536
    event_byte_cap: int = 128 * 1024 * 1024
    query_byte_cap: int = 8 * 1024 * 1024
    research_allocation_id: str = ""
    action_seconds: float = 90.0
    max_invocations: int = 8
    research_seconds: float = 0.0
    campaign_id: str = ""
    family_id: str = ""

    def __post_init__(self) -> None:
        MemoryMode(self.mode)
        if self.theory_mode not in {"off", "read", "build"}:
            raise ValueError("unknown Mini theory mode")
        text(self.root, "memory root", required=False)
        if self.root:
            object.__setattr__(
                self, "root", os.path.abspath(Path(self.root).expanduser())
            )
        text(self.research_allocation_id, "research allocation", required=False)
        text(self.campaign_id, "campaign", required=False)
        text(self.family_id, "family", required=False)
        if self.mode != "off" and not self.root:
            raise ValueError("enabled memory requires an explicit root")
        if self.mode == "develop" and (
            self.theory_mode != "build"
            or not self.research_allocation_id
            or self.research_seconds <= 0
        ):
            raise ValueError(
                "develop requires theory build and an explicit research allocation"
            )
        for name in (
            "cheap_candidate_cap",
            "prepared_candidate_cap",
            "probe_cap",
            "outbox_event_cap",
            "outbox_byte_cap",
            "artifact_byte_cap",
            "artifact_store_byte_cap",
            "artifact_count_cap",
            "query_scan_cap",
            "event_count_cap",
            "event_byte_cap",
            "query_byte_cap",
            "max_invocations",
        ):
            integer(getattr(self, name), name, 1)
        hard_limits = {
            "cheap_candidate_cap": 4096,
            "prepared_candidate_cap": 256,
            "probe_cap": 64,
            "outbox_event_cap": 4096,
            "outbox_byte_cap": 64 * 1024 * 1024,
            "artifact_byte_cap": 16 * 1024 * 1024,
            "artifact_store_byte_cap": 512 * 1024 * 1024,
            "artifact_count_cap": 65536,
            "query_scan_cap": 4096,
            "event_count_cap": 65536,
            "event_byte_cap": 128 * 1024 * 1024,
            "query_byte_cap": 8 * 1024 * 1024,
            "max_invocations": 1024,
        }
        for name, limit in hard_limits.items():
            if getattr(self, name) > limit:
                raise ValueError(f"{name} exceeds the memory hard limit")
        for name in ("action_seconds", "research_seconds"):
            value = getattr(self, name)
            if type(value) not in (int, float) or not math.isfinite(value) or value < 0:
                raise ValueError(f"{name} requires finite nonnegative seconds")
        if self.research_seconds > self.action_seconds:
            raise ValueError("research allowance must fit inside the memory allocation")
        if (
            self.prepared_candidate_cap > self.cheap_candidate_cap
            or self.probe_cap > self.prepared_candidate_cap
        ):
            raise ValueError(
                "memory caps require probes <= prepared <= cheap candidates"
            )

    @property
    def enabled(self) -> bool:
        return self.mode != "off"

    @property
    def probes_enabled(self) -> bool:
        return self.mode in {"assist", "develop"}

    @property
    def generalization_enabled(self) -> bool:
        return self.mode == "develop"

    def to_record(self) -> dict:
        return {name: getattr(self, name) for name in self.__dataclass_fields__}

    @classmethod
    def from_record(cls, record: dict) -> MemoryConfig:
        return cls(**record)
