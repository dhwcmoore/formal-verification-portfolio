Require Import SafetyCore.
Require Import Reals.
Require Import Lra.
Require Import QArith.

Open Scope R_scope.

Module FDA_Medical_Device.
  Import SafetyCore.

  (* Proof friendly, real valued constant *)
  Definition fda_precision_requirement : R := 1.0e-12.

  (* Extraction friendly constant: exactly 10^-12 as a rational *)
  Definition fda_precision_requirement_q : Q := (1 # 1000000000000).

  Theorem fda_precision_stricter :
    fda_precision_requirement < SafetyCore.safety_precision_requirement.
  Proof.
    unfold fda_precision_requirement, SafetyCore.safety_precision_requirement.
    lra.
  Qed.

End FDA_Medical_Device.
