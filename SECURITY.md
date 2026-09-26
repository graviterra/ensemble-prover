# Security Policy

## Supported versions

Security fixes are maintained on the latest revision of `main`, covering Mini
Prover, natural-language input, formalization campaigns, and the local browser
interface. Tags are fixed snapshots: subsequent fixes on `main` do not change
previously downloaded archives. Update to the latest `main` revision to receive
fixes, and include the exact commit when reporting a problem. Older releases
are not separate security-maintenance branches. Generated proofs, run dossiers,
and campaign exports are artifacts, not supported software release lines.

## Reporting a vulnerability

Use GitHub's [private vulnerability reporting form](https://github.com/graviterra/ensemble-prover/security/advisories/new).
Do not open a public issue for an unpatched vulnerability. Never include API
keys or other credentials. Use a sanitized reproduction instead of uploading
private theorem sources, model transcripts, or complete run directories.

Include the affected commit, entry point or command, minimal reproduction,
expected impact, and relevant operating-system, Python, Lean/Mathlib, and
provider details. Credential exposure, unintended provider disclosure,
unsafe subprocess handling, tampered artifact acceptance, and bypasses of
proof verification are especially important to report.

There is no guaranteed response-time SLA.

## Operational guidance

- Lean elaboration and Lake builds can execute code. Use trusted projects and
  dependencies, or an appropriately isolated container or virtual machine
  with restricted files, credentials, and network access. A Python virtual
  environment is not a security boundary.
- Provider keys and recognized credential-like variables are filtered from
  local-tool child environments. Trusted internal provider workers retain the
  credentials they need. On Linux, credential-bearing processes are made
  non-dumpable to restrict same-user descendant `/proc` access. This is not a
  complete sandbox or protection against privileged processes.
- Environment filtering does not prevent hostile code from reading accessible
  files, including `.env`, or using the prover user's network privileges.
  Keep keys out of source control and shared artifacts; restrict their scope
  and rotate any exposed credentials.
- Provider cooldown identities use a keyed credential fingerprint. Its private
  installation key lives under `${XDG_STATE_HOME:-~/.local/state}/ensemble-prover/`
  with access restricted to the owner. Keep this key separate from shared run
  artifacts. This protects against guessing credentials from fingerprints; it
  does not protect against a process able to read the private key itself.
- Configured providers may receive theorem statements, source passages,
  definitions, retrieved context, proof plans, attempts, and Lean diagnostics.
  Submit confidential material only when you are authorized to share it with
  those providers. This applies to formalizers and reviewers as well as provers.
- Run dossiers, campaign ledgers, transcripts, caches, and exports may contain
  private mathematics and local paths. Review them before sharing. Do not
  share mutable caches or campaign state between mutually untrusted users.

## Proof and formalization trust

Lean verification concerns the exact formal statement and its dependencies;
it does not certify that a natural-language translation captures the intended
mathematics. Inspect generated definitions and statements even after model
review. An unproved `--formalize-only` output, a paused campaign, or an exit
status of zero alone is not evidence of a solved theorem.

Require the workflow's verified completion and export checks before treating
an artifact as proved. Preserve the recorded Lean environment and provenance;
do not bypass mismatches by editing fingerprints, receipts, or campaign state.
The Lean toolchain and trusted project dependencies remain part of the trust
boundary.

See the [User Guide](docs/USER_GUIDE.md#15-security-privacy-and-operational-safety)
for operational details and the workflow-specific completion checks.

## Local browser service

The optional browser service binds only to `127.0.0.1`. It assumes a trusted
local user and trusted run and service-state directories. Read-only operation
is the default; `--control` enables launches and cooperative stop requests for
owned processes. Host, origin, and fetch-metadata checks restrict browser
requests, and mutations require a per-service capability.

These controls do not provide remote user authentication or isolate local
accounts. Do not expose the service through a network proxy, forward its port,
or deploy it as a shared internet service. A provider-enabled launch can spend
money and execute code from the selected Lean project. Supply credentials in
the service environment and keep private sources and recorded output local.
