
type __ = Obj.t

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

val pred : nat -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val pow : nat -> nat -> nat
 end

module Pos :
 sig
  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val size_nat : positive -> nat

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_nat : nat -> positive

  val of_succ_nat : nat -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val compare : z -> z -> comparison

  val sgn : z -> z

  val max : z -> z -> z

  val min : z -> z -> z

  val abs : z -> z

  val to_nat : z -> nat

  val of_nat : nat -> z

  val to_pos : z -> positive

  val ggcd : z -> z -> (z, (z, z) prod) prod
 end

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qlt_le_dec : q -> q -> sumbool

val qarchimedean : q -> positive

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val qred : q -> q

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

type string =
| EmptyString
| String of ascii * string

val qabs : q -> q

val linear_search_conform : (nat -> sumbool) -> nat -> nat

val linear_search_from_0_conform : (nat -> sumbool) -> nat

val constructive_indefinite_ground_description_nat : (nat -> sumbool) -> nat

val p'_decidable : (nat -> 'a1) -> ('a1 -> sumbool) -> nat -> sumbool

val constructive_indefinite_ground_description :
  ('a1 -> nat) -> (nat -> 'a1) -> ('a1 -> sumbool) -> 'a1

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

val qbound_ltabs_ZExp2 : q -> z

val z_inj_nat : z -> nat

val z_inj_nat_rev : nat -> z

val constructive_indefinite_ground_description_Z : (z -> sumbool) -> z

type cReal = { seq : (z -> q); scale : z }

type cRealLt = z

type cReal_appart = (cRealLt, cRealLt) sum

val cRealLt_lpo_dec :
  cReal -> cReal -> (__ -> (nat -> sumbool) -> nat sumor) -> (cRealLt, __) sum

val inject_Q : q -> cReal

val cReal_plus_seq : cReal -> cReal -> z -> q

val cReal_plus_scale : cReal -> cReal -> z

val cReal_plus : cReal -> cReal -> cReal

val cReal_opp_seq : cReal -> z -> q

val cReal_opp_scale : cReal -> z

val cReal_opp : cReal -> cReal

val cReal_mult_seq : cReal -> cReal -> z -> q

val cReal_mult_scale : cReal -> cReal -> z

val cReal_mult : cReal -> cReal -> cReal

val cRealLowerBound : cReal -> cRealLt -> z

val cReal_inv_pos_cm : cReal -> cRealLt -> z -> z

val cReal_inv_pos_seq : cReal -> cRealLt -> z -> q

val cReal_inv_pos_scale : cReal -> cRealLt -> z

val cReal_inv_pos : cReal -> cRealLt -> cReal

val cReal_neg_lt_pos : cReal -> cRealLt -> cRealLt

val cReal_inv : cReal -> cReal_appart -> cReal

val cRealLtDisjunctEpsilon :
  cReal -> cReal -> cReal -> cReal -> (cRealLt, cRealLt) sum

val sig_forall_dec : (nat -> sumbool) -> nat sumor

val lowerCutBelow : (q -> bool) -> q

val lowerCutAbove : (q -> bool) -> q

type dReal = (q -> bool)

val dRealQlim_rec : (q -> bool) -> nat -> nat -> q

val dRealAbstr : cReal -> dReal

val dRealQlim : dReal -> nat -> q

val dRealQlimExp2 : dReal -> nat -> q

val cReal_of_DReal_seq : dReal -> z -> q

val cReal_of_DReal_scale : dReal -> z

val dRealRepr : dReal -> cReal

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

val total_order_T :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> sumbool sumor

val req_appart_dec :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> sumbool

val rrepr_appart_0 : RbaseSymbolsImpl.coq_R -> cReal_appart

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

val q2R : q -> RbaseSymbolsImpl.coq_R

module SafetyCore :
 sig
  val safety_margin : RbaseSymbolsImpl.coq_R

  val safety_precision_requirement : RbaseSymbolsImpl.coq_R

  type coq_SimpleBoundary = { lower_bound : RbaseSymbolsImpl.coq_R;
                              upper_bound : RbaseSymbolsImpl.coq_R;
                              name : string }

  type safety_critical = __
 end
