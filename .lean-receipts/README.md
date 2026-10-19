# Receipts

## `067501d`: lower-tier receipt, Slurm job 5586731

- Receipt: `067501d7208c-slurm-5586731.json`. Slurm job `5586731`: COMPLETED, exit `0:0`,
  elapsed 00:03:56, TotalCPU 04:36.686.
- Checker: lean-pkg 0.7.49 template (SRC_MODE=clone, DEPS_TAR) gate: lake build of the library and both Solution modules + serial lake env leanchecker -v over every library and Solution module (checker-loop-ncl) + lake lean #print axioms over all claims.yaml declarations (gen_axioms-ncl); Easley Slurm, glibc-2.35 container, node-local toolchain; sorry_count 0; axioms Classical.choice, Quot.sound, propext.
- Log: `067501d7208c-slurm-5586731-verify.redacted.log`, SHA-256 `7d6c7341da022729ec4582a55df703034ffecb11671be1bbe6746c5557ef231b` (= `report_sha256`);
  raw log SHA-256 `7d6c7341da022729ec4582a55df703034ffecb11671be1bbe6746c5557ef231b` (0 line(s) differ: per-job paths redacted).
- Seal: job stdout SHA-256 `db3c30da48bb6b852c0fdab88edd1afda5319c986ca2de6b1176337b69ebcd85` carries verify-log-sha256 = raw log SHA-256 `7d6c7341da022729ec4582a55df703034ffecb11671be1bbe6746c5557ef231b`; lake-manifest.json SHA-256 `b01bd50494f2f857fba128e85332ef07930bedb20605995ada7a9f22e81c418c` (pre = post).
Standard gate of v0.1.0 on the Auburn Easley cluster: stock lean-pkg template (SRC_MODE=clone; pinned dependencies restored from a hash-checked tarball, Mathlib cache staged node-local from a hash-checked tar); lake build of the library and both comparator Solution modules, serial leanchecker over all 15 library and Solution modules (15/15), #print axioms over all 181 claims (standard three only). Paired with the comparator receipt 067501d7208c-comparator.json (37/37 full, 13/13 headline; Lean, con-ron and nanoda kernels). 4 CPUs, 3 min 56 s.
