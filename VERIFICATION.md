# Verification record

The supplied package was built and audited on 2026-10-12 using the official
Lean 4.19.0 Linux distribution (commit 6caaee842e94).

- `lake build`: exit code 0.
- `lake env lean -DwarningAsError=true Audit.lean`: exit code 0.
- Both final theorem dependencies: `propext`, `Quot.sound`.
- The supplied proof file is unchanged from the previously delivered single-file
  formalization.

The local sandbox required a launcher compatibility shim to report the current
process executable path correctly. This did not modify Lean, its libraries, or
any proof source. It is not included in or required by the GitHub workflow.
A successful local run does not claim that the workflow has already run on GitHub.

Proof file SHA-256: `ef6eb9a322c51a5d3fb522f272df663c46c98f9f40888328c7e933d7e98507cd`
