(* extract_fda.v *)

From Coq Require Import Extraction.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.

From VeriboundCore Require Import FDA_Device_Safety.

Extraction Language OCaml.

Extraction "extracted_fda.ml" FDA_Medical_Device.fda_precision_requirement.
