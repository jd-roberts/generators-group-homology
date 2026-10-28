# ONE authorized prime-7 known-identity control

[Technical report](../../../docs/CERTIFIED-POWER-CONTROL.md).

This consumed the authorization for ONE bounded experiment on the already
certified R12=z^7. Both methods ran in one worker with one shared one-second
alarm, a combined 128-rule ceiling, and the specified OS caps. No fifteen-target
search or new arithmetic target was attempted. Do not rerun the controller.

- `control-attempt.json`: exclusive one-shot reservation, source/gate hashes.
- `source/`: exact search, adapter, checker and guard snapshots.
- `full-input.json.gz`: unchanged original 236-row quotient blueprint.
- `control-input.json`: only Q225,Q140,Q204, in local length order, and R12.
- `worker/stdout.txt`: exact complete JSONL input header, method start/result
  checkpoints, all local AND original-index rule/target proofs, and shared
  clock summary. `stderr.txt` is empty.
- `worker/resources.json`: exact effective OS caps, CPU/wall/RSS, successful
  termination, output bytes and cleanup status.
- `result.json` and `independent-check.*`: separate independent checker accepts
  all 47 rules, 25 compiler target factors and 90 completion target factors
  against the original Q. No source relator outside the three selected rows
  appears in any new certificate.
- `post-replay.stdout.txt`: certificate-only final replay including the small
  suite; it does not run either search engine.
- `stage1/`: eight passing safety probes, eleven old verification commands,
  three constrained small workers and their exact logs/resources. The
  whitespace-bearing paper-provenance stdout is preserved losslessly as gzip. The small
  three-method gate is stored separately in the sibling comparison directory.

Both methods succeed on the known control. Five originals remain certified:
R3,R5,R9,R12,R15. Full spanning remains unresolved; there is no new homology,
independence, nontriviality or exact-dimension result. The old 33-factor R12
certificate and all previously certified evidence are preserved unchanged.

Use `scripts/check-power-control.py --base` on this directory for independent
certificate-only verification. The attempt marker blocks another launch at
this location; another directory is not authorization for another trial.
