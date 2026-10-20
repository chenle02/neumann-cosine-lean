# Receipts

## `067501d`: lower-tier receipt, Slurm job 5586731

- Receipt: `067501d7208c-slurm-5586731.json`. Slurm job `5586731`: COMPLETED, exit `0:0`,
  elapsed 00:03:56, TotalCPU 04:36.686.
- Checker: lean-pkg 0.7.49 template (SRC_MODE=clone, DEPS_TAR) gate: lake build of the library and both Solution modules + serial lake env leanchecker -v over every library and Solution module (checker-loop-ncl) + lake lean #print axioms over all claims.yaml declarations (gen_axioms-ncl); Easley Slurm, glibc-2.35 container, node-local toolchain; sorry_count 0; axioms Classical.choice, Quot.sound, propext.
- Log: `067501d7208c-slurm-5586731-verify.redacted.log`, SHA-256 `7d6c7341da022729ec4582a55df703034ffecb11671be1bbe6746c5557ef231b` (= `report_sha256`);
  raw log SHA-256 `7d6c7341da022729ec4582a55df703034ffecb11671be1bbe6746c5557ef231b` (0 line(s) differ: per-job paths redacted).
- Seal: job stdout SHA-256 `db3c30da48bb6b852c0fdab88edd1afda5319c986ca2de6b1176337b69ebcd85` carries verify-log-sha256 = raw log SHA-256 `7d6c7341da022729ec4582a55df703034ffecb11671be1bbe6746c5557ef231b`; lake-manifest.json SHA-256 `b01bd50494f2f857fba128e85332ef07930bedb20605995ada7a9f22e81c418c` (pre = post).
Standard gate of v0.1.0 on the Auburn Easley cluster: stock lean-pkg template (SRC_MODE=clone; pinned dependencies restored from a hash-checked tarball, Mathlib cache staged node-local from a hash-checked tar); lake build of the library and both comparator Solution modules, serial leanchecker over all 15 library and Solution modules (15/15), #print axioms over all 181 claims (standard three only). Paired with the comparator receipt 067501d7208c-comparator.json (37/37 full, 13/13 headline; Lean, con-ron and nanoda kernels). 4 CPUs, 3 min 56 s.

## `067501d`: lower-tier receipt, Slurm job 5586732

- Receipt: `067501d7208c-slurm-5586732.json`. Slurm job `5586732`: COMPLETED, exit `0:0`,
  elapsed 05:31:20, TotalCPU 08:19:25.
- Checker: lean-pkg 0.7.49 template (SRC_MODE=clone, no DEPS_TAR, empty Mathlib cache) cold build: Lake clones every pinned dependency from GitHub and compiles Mathlib and the library from source; then serial leanchecker over every library and Solution module and #print axioms over all claims; Easley Slurm, glibc-2.35 container; sorry_count 0; axioms Classical.choice, Quot.sound, propext.
- Log: `067501d7208c-slurm-5586732-verify.redacted.log`, SHA-256 `100d3def2f77af5038100d6a8d6b3c27c3df0246800f493128051146642865e7` (= `report_sha256`);
  raw log SHA-256 `100d3def2f77af5038100d6a8d6b3c27c3df0246800f493128051146642865e7` (0 line(s) differ: per-job paths redacted).
- Stored compressed: `067501d7208c-slurm-5586732-verify.redacted.log.gz` (deterministic gzip, SHA-256 `be501e45e96775d34276f0e81b7796975bf59946420b37aefda3a6c86249a955` = `report_compressed.sha256`; 654086 bytes uncompressed). Restore: `gzip -dc 067501d7208c-slurm-5586732-verify.redacted.log.gz > 067501d7208c-slurm-5586732-verify.redacted.log`, then `sha256sum 067501d7208c-slurm-5586732-verify.redacted.log` prints `report_sha256`.
- Seal: job stdout SHA-256 `4e1afc97dc579a870a5bad4f667d65ad379c744727ec3972959bf0897a0fcb4e` carries verify-log-sha256 = raw log SHA-256 `100d3def2f77af5038100d6a8d6b3c27c3df0246800f493128051146642865e7`; lake-manifest.json SHA-256 `b01bd50494f2f857fba128e85332ef07930bedb20605995ada7a9f22e81c418c` (pre = post).
Cold build of v0.1.0 on the Auburn Easley cluster with no caches: Lake cloned every pinned dependency from GitHub (Mathlib 56a005855ea1) and compiled all 8,624 Mathlib modules and the library from source; then leanchecker over all 15 library and Solution modules (15/15) and #print axioms over all 181 claims (standard three only). 5 h 31 min on 24 allocated CPUs.
