# Formal Verification Portfolio

This repository presents a small number of high-leverage artefacts demonstrating boundary-aware formal verification, systems discipline, and proof-guided engineering. The emphasis is not on volume, but on clarity of architectural judgement and correctness under explicit constraints.

The projects collected here share a common thesis:

> Verification success within a layer does not entail correctness relative to the surrounding system unless boundary conditions are explicitly enforced.

---

## Fast entry points

### 1. VeriBound  
**Auditability beyond self-certification**

`projects/veribound/`

VeriBound is a boundary-enforced audit architecture that produces explicit, sealed audit traces rather than relying on internal claims of correctness.

The system implements the **Production–Closure Separation** proven in the companion work on boundary discipline and the structural limits of internal certification. In short: generation and certification cannot safely reside in the same layer.

**What to look at first**
- `projects/veribound/docs/`  
  Minimal demo artefacts showing input data and the resulting audit trace.
- `projects/veribound/src/`  
  Coq and OCaml sources defining boundary predicates, admissibility conditions, and extracted verification logic.
- `projects/veribound/paper/`  
  Companion theoretical material motivating the architecture.

VeriBound is intended to be legible in seconds and defensible over hours.

---

### 2. Parallelised Topological Data Analysis (OCaml)

This track develops a cosheaf-based approach to persistent homology with explicit attention to correctness boundaries, performance, and multicore execution.

The aim is to demonstrate that mathematical sophistication and systems engineering discipline can coexist in production-grade code.

**Key elements**
- OCaml implementations of algebraic kernels
- A plan for multicore parallelisation using OCaml 5 Domains
- A browser-based demonstration path via WebAssembly

This project serves as a contrast case: high-performance computation paired with explicit correctness assumptions rather than implicit guarantees.

---

## Repository structure
.
├── projects/
│ └── veribound/
│ ├── README.md
│ ├── docs/
│ ├── src/
│ └── paper/
├── papers/
├── README.md
└── LICENSE


---

## Design principles

The work collected here is guided by a small number of non-negotiable principles:

1. **Explicit boundaries**  
   Every guarantee is relative to a declared scope. No global correctness claims are made without boundary conditions.

2. **Separation of concerns**  
   Productive computation and certification are treated as distinct phases with distinct responsibilities.

3. **Auditability as a first-class object**  

O

   Verification produces an artefact, not a feeling. If it cannot be inspected, replayed, or invalidated, it does not count.

4. **Minimal surface area**  
   Each project is structured so that a reviewer can identify the core idea without traversing the entire codebase.

---

## How to read this repository

If you have limited time:

1. Open `projects/veribound/docs/`
2. Read the example input and output audit trace
3. Skim `projects/veribound/README.md`

If you want the formal core:

- Follow the Coq sources under `projects/veribound/src/coq/`
- Consult the companion paper material for the underlying separation results

If you are interested in performance and systems design:

- Explore the TDA track and its planned multicore and WebAssembly deployment

---

## Status

This repository is intentionally curated rather than exhaustive. Each included artefact represents a stable conceptual position, not a transient experiment.

Further material may be added only when it sharpens, rather than dilutes, the architectural narrative.

---

## Licence

Unless otherwise noted, all original code and text in this repository is released under the MIT Licence. Third-party dependencies retain their original licensing terms.

---

## Contact

This portfolio is intended to support technical discussion rather than marketing.  
If something here is unclear, that is a design failure, not a rhetorical choice.
