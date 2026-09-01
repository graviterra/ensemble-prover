# Security Policy

## Supported versions

Version 1.0.2 is the current supported release. Version 1.0.1 added subprocess
credential isolation but is superseded because it pinned a vulnerable
`python-dotenv` release. Version 1.0.0 is the initial public release and is
superseded because local-tool subprocesses directly inherited provider
credentials. Security fixes are applied to the latest revision of the default
branch; older snapshots and generated run artifacts are not supported release
lines.

## Reporting a vulnerability

Please report suspected vulnerabilities privately through the repository's
GitHub Security Advisory interface. Do not open a public issue for an
unpatched vulnerability and do not include provider credentials, private
theorem sources, model transcripts, or generated run dossiers in a report.

Include the affected revision, a minimal reproduction, expected impact, and
any relevant environment details. Reports involving untrusted Lean projects,
subprocess isolation, credential exposure, provider data disclosure, or proof
acceptance without Lean verification are especially important.

There is no guaranteed response-time SLA.

## Operational guidance

- Keep API keys in an ignored `.env` file or a dedicated secret manager.
- Use isolated compute for untrusted Lean projects and model-generated tools.
- Provider keys and a denylist of common credential variables are removed from
  local-tool child environments. Credential-bearing parent processes are
  non-dumpable on Linux to block descendant `/proc` inspection. These controls
  are not a filesystem, network, or operating-system sandbox.
- Review what theorem context a configured external provider will receive.
- Treat only independently Lean-accepted artifacts as proofs.
- Do not publish raw run directories without reviewing prompts, responses,
  paths, environment metadata, and theorem sources for sensitive content.
