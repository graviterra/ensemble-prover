# Security Policy

## Supported versions

This project is currently a research preview. Security fixes are applied to the
latest revision of the default branch; older snapshots and generated run
artifacts are not supported release lines.

## Reporting a vulnerability

Please report suspected vulnerabilities privately through the repository's
GitHub Security Advisory interface. Do not open a public issue for an
unpatched vulnerability and do not include provider credentials, private
theorem sources, model transcripts, or generated run dossiers in a report.

Include the affected revision, a minimal reproduction, expected impact, and
any relevant environment details. Reports involving untrusted Lean projects,
subprocess isolation, credential exposure, provider data disclosure, or proof
acceptance without Lean verification are especially important.

There is no guaranteed response-time SLA during the research-preview phase.

## Operational guidance

- Keep API keys in an ignored `.env` file or a dedicated secret manager.
- Use isolated compute for untrusted Lean projects and model-generated tools.
- Review what theorem context a configured external provider will receive.
- Treat only independently Lean-accepted artifacts as proofs.
- Do not publish raw run directories without reviewing prompts, responses,
  paths, environment metadata, and theorem sources for sensitive content.

