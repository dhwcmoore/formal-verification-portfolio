# VeriBound

Verification success within a layer does not entail correctness relative to the surrounding system unless boundary conditions are explicitly enforced.

This system implements the Production–Closure Separation proven in *Boundary Discipline and the Structural Limits of Internal Certification*.

## How to build (Rocq/Coq)

From `src/coq`:

```bash
make
```

## What this repo is for

A recruiter will not install your tool. This repo is structured so they can:

1) Watch a short demo in `docs/`
2) See the formal core in `src/coq/VeriboundCore/`
3) Read the companion paper in `paper/`
