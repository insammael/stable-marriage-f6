# Verification record

This directory contains the public evidence used for the v08 pre-push audit.

- `audit_summaries/`: frozen v07 audit records.
- `certificates/`: the reproducible explicit-example checker and expected JSON.
- `THEOREM_DIFF.txt`: theorem-statement comparison between v07 and v08.
- `LEAN_BUILD.txt`: sanitized successful Lean/Lake build result.
- `LEAN_COMPATIBILITY_DIFF.txt`: the single proof-syntax-only compatibility
  hunk relative to frozen v07.
- `AXIOM_AUDIT.txt`: kernel axiom report for the advertised theorem.
- `SORRY_ADMIT_SCAN.txt`: scoped admission scan distinguishing the deliberate
  Challenge hole from the proof development and Solution.
- `PUBLIC_SAFETY_SCAN.txt`: public-content scan results.
- `PALOMAR_CHECKS.txt`: current schema checks and execution availability.
- `PALOMAR_BUILD.log`: successful Challenge/Solution surface build record.
- `SHA256SUMS.txt`: hashes of all regular files in the candidate, except the
  hash file itself.

Remote-only Palomar checks are explicitly recorded as deferred rather than
silently omitted.
