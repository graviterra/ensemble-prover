"""Typed, federated mathematical retrieval for Mini proof search."""

from .model import (
    CandidateOrigin,
    RetrievalCandidate,
    RetrievalQuery,
    RetrievalResult,
    RetrievalSourcePolicy,
    RetrievalSourceReport,
)
from .service import (
    AnswerSafePreambleSource,
    FederatedSearchHit,
    MathematicalRetrievalService,
    ProjectSupportSource,
    PublishedTheorySource,
    StaticMathlibSource,
    VerifiedHelperSource,
)

__all__ = [
    "AnswerSafePreambleSource",
    "CandidateOrigin",
    "FederatedSearchHit",
    "MathematicalRetrievalService",
    "ProjectSupportSource",
    "PublishedTheorySource",
    "RetrievalCandidate",
    "RetrievalQuery",
    "RetrievalResult",
    "RetrievalSourcePolicy",
    "RetrievalSourceReport",
    "StaticMathlibSource",
    "VerifiedHelperSource",
]
