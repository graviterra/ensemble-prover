"""Certificate-gated conjecture and helper falsification for Mini.

Heuristic engines in this package may discover counterexample candidates, but
only :class:`LeanCounterexampleCertificate` records with ``authoritative`` set
may change proof-search state.  This separation is the package's central trust
boundary.
"""

from .model import (
    CounterexampleCandidate,
    FalsificationFinding,
    FalsificationOutcome,
    FalsificationReport,
    LeanCounterexampleCertificate,
    TargetKind,
    TrustLevel,
    authoritative_certificate_record_is_valid,
    certificate_record_is_valid,
    falsification_report_record_is_valid,
)
from .policy import (
    DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S,
    DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S,
    DEFAULT_FALSIFICATION_PROBE_TIMEOUT_S,
    FalsificationPolicy,
    instance_probe_timeout_s,
    require_falsification_search_bound,
    require_falsification_watchdog,
)
from .veto import (
    DEFAULT_FALSIFICATION_VETO_ENGINES,
    DEFAULT_FALSIFICATION_VETO_SEARCH_TIMEOUT_S,
    cheap_veto_skip_key,
    make_falsification_veto_policy,
)
from .certificate import (
    CertificationResult,
    CertificationStatus,
    certify_candidate_result,
)
from .service import FalsificationService

__all__ = [
    "CounterexampleCandidate",
    "CertificationResult",
    "CertificationStatus",
    "DEFAULT_FALSIFICATION_ENGINE_TIMEOUT_S",
    "DEFAULT_FALSIFICATION_OPERATION_TIMEOUT_S",
    "DEFAULT_FALSIFICATION_PROBE_TIMEOUT_S",
    "DEFAULT_FALSIFICATION_VETO_ENGINES",
    "DEFAULT_FALSIFICATION_VETO_SEARCH_TIMEOUT_S",
    "cheap_veto_skip_key",
    "instance_probe_timeout_s",
    "make_falsification_veto_policy",
    "certify_candidate_result",
    "FalsificationFinding",
    "FalsificationOutcome",
    "FalsificationPolicy",
    "require_falsification_search_bound",
    "require_falsification_watchdog",
    "FalsificationReport",
    "FalsificationService",
    "LeanCounterexampleCertificate",
    "TargetKind",
    "TrustLevel",
    "authoritative_certificate_record_is_valid",
    "certificate_record_is_valid",
    "falsification_report_record_is_valid",
]
