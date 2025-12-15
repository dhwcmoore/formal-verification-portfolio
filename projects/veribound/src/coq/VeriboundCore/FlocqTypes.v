(* FlocqTypes.v *)

From Coq Require Import Reals.Reals.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
From Coq Require Import Bool.Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope R_scope.

From Flocq Require Import IEEE754.Bits.
From Flocq Require Import IEEE754.Binary.

(* IEEE-754 double precision *)
Definition float64 := binary64.

(* Stable coercion used throughout the project *)
Definition B2R64 (x : float64) : R := B2R 53 1024 x.

Record VerifiedBoundary := {
  lower_float : float64;
  upper_float : float64;
  category    : string
}.

Record VerifiedDomain := {
  domain_name : string;
  boundaries  : list VerifiedBoundary
}.

Definition in_boundary_range (x : float64) (b : VerifiedBoundary) : bool :=
  let xr := B2R64 x in
  let lo := B2R64 b.(lower_float) in
  let hi := B2R64 b.(upper_float) in
  if Rle_dec lo xr then
    if Rle_dec xr hi then true else false
  else false.

Fixpoint find_category_flocq (bs : list VerifiedBoundary) (x : float64) : option string :=
  match bs with
  | [] => None
  | b :: bs' =>
      if in_boundary_range x b
      then Some b.(category)
      else find_category_flocq bs' x
  end.
