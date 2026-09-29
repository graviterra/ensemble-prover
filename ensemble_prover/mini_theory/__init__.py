"""Persistent, Mini-owned Lean domain theory.

The proof-state lemma cache accelerates one proof search.  This package owns a
different boundary: immutable Lean modules that have been verified without the
active problem preamble and may therefore be imported by later problems.
"""

from .model import (
    MINI_THEORY_SCHEMA_VERSION,
    PublishedTheoryBundle,
    TheoryBundleCandidate,
    TheoryDeclaration,
    TheoryNeed,
    TheoryVerificationReceipt,
)
from .need_store import TheoryNeedRecord, TheoryNeedStore
from .policy import TheoryPolicy, TheoryPolicyVerdict
from .context import TheoryContext, TheoryContextPair
from .builder import (
    LLMTheoryCandidateBuilder,
    TheoryCandidateBuilder,
    TheoryCandidateOutputUnavailable,
)
from .library import MiniTheoryLibrary, TheoryMode, TheoryPublishResult
from .retrieval import MiniTheoryRetriever, TheorySearchHit
from .promotion import HelperPromotionResult, VerifiedHelperPromoter
from .promotion_outbox import (
    PromotionDrainReport,
    PromotionEnqueueResult,
    PromotionOutbox,
    PromotionOutboxEntry,
    helper_is_promotable,
    run_verified_helper_promotion_maintenance,
)
from .store import (
    TheoryStoreConflict,
    TheoryStoreError,
    TheoryStorePublicationCommitted,
)
from .verifier import TheoryBundleVerifier, TheoryVerificationResult

__all__ = [
    "MINI_THEORY_SCHEMA_VERSION",
    "PublishedTheoryBundle",
    "MiniTheoryRetriever",
    "MiniTheoryLibrary",
    "LLMTheoryCandidateBuilder",
    "TheoryBundleCandidate",
    "TheoryCandidateBuilder",
    "TheoryCandidateOutputUnavailable",
    "TheoryBundleVerifier",
    "TheoryContext",
    "TheoryContextPair",
    "TheoryMode",
    "TheoryNeedRecord",
    "TheoryNeedStore",
    "TheoryPublishResult",
    "TheoryDeclaration",
    "TheoryNeed",
    "TheoryPolicy",
    "TheoryPolicyVerdict",
    "TheoryStoreConflict",
    "TheoryStoreError",
    "TheoryStorePublicationCommitted",
    "TheorySearchHit",
    "HelperPromotionResult",
    "VerifiedHelperPromoter",
    "PromotionDrainReport",
    "PromotionEnqueueResult",
    "PromotionOutbox",
    "PromotionOutboxEntry",
    "helper_is_promotable",
    "run_verified_helper_promotion_maintenance",
    "TheoryVerificationReceipt",
    "TheoryVerificationResult",
]
