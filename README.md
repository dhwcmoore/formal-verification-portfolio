# Boundary Discipline & Formal Verification for AI Safety

**Author:** [Duston Moore]
**Role:** Independent AI Safety Researcher & Formal Verification Engineer
**Specialization:** Type Theory, OCaml, Mechanistic Interpretability, Process Philosophy

---

## 🚀 Research Agenda: The Production-Closure Separation

Current AI safety approaches often rely on probabilistic guardrails (RLHF, Constitutional AI) to police generative outputs. My research argues that this approach is structurally insufficient for safety-critical domains.

I have formally proven the **Production-Closure Separation Theorem** (see [Paper](./papers/bd3.pdf)), which demonstrates that:
> *No generative system (Production) can internally certify its own completion conditions (Closure) without an external, boundary-constrained kernel.*

This repository contains the **reference implementation** of a solution: a formal verification kernel (VeriBound) that enforces "Boundary Discipline" via OCaml type systems and Coq-extracted logic.

---

## 🔬 Technical Deep Dive: From Theory to Code

This implementation prevents "Ontological Misalignment" (hallucination of safety) by enforcing a strict architectural boundary.

### 1. The Kernel Interface (Architecture)
**File:** [`/core/common/engine_interface.ml`](./veribound_dev/core/common/engine_interface.ml)

To enforce the separation of concerns, I isolate the verification logic behind a strict functorial interface. This guarantees that the *generative* component cannot modify the *certifying* component's internal state.

```ocaml
module type CLASSIFICATION_ENGINE = sig
  val engine_name : string
  val precision_guarantee : string
  (* Enforces explicit boundary distance checks rather than probabilistic confidence *)
  val boundary_distance : domain -> float -> float
end
