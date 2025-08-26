(** This file is part of CoqEAL, the Coq Effective Algebra Library.
(c) Copyright INRIA and University of Gothenburg, see LICENSE *)
From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
From mathcomp Require Import tuple.
From mathcomp Require Import ssralg fintype finfun perm matrix bigop zmodp mxalgebra.
From mathcomp Require Import choice poly polydiv mxpoly binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** This file contains definitions and lemmas that are generic enough that
we could try to integrate them in Math Components' library.
Definitions and theories are gathered according to the file of the
library which they could be moved to. *)

(** ** Informative version of [iff] *)

(** As CoqEAL now puts all relations in [Type], we define a compliant
version of [iff], named [ifft], along with view declarations *)
Inductive ifft (A B : Type) : Type := Ifft of (A -> B) & (B -> A).
Infix "<=>" := ifft (at level 95) : type_scope.

Section ApplyIfft.

Variables P Q : Type.
Hypothesis eqPQ : P <=> Q.

Lemma ifft1 : P -> Q. Proof. by case: eqPQ. Qed.
Lemma ifft2 : Q -> P. Proof. by case: eqPQ. Qed.

End ApplyIfft.

Hint View for move/ ifft1|2 ifft2|2.
Hint View for apply/ ifft1|2 ifft2|2.

Lemma ifftW (P Q : Prop) : P <=> Q -> (P <-> Q).
Proof. by case. Qed.

(********************* seq.v *********************)
Section Seq.

Variables (T1 T2 T3 : Type) (f : T1 -> T2 -> T3).

Lemma seq2_ind (P : seq T1 -> seq T2 -> Prop) : P [::] [::] ->
 (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
  forall s1 s2, size s1 = size s2 -> P s1 s2.
Proof.
move=> Pnil Pcons.
elim=> [|x1 l1 IH1]; case=> // x2 l2 /eqnP /= Hs.
by apply/Pcons/IH1/eqnP.
Qed.

End Seq.

Section Seqeqtype.

Variable T : eqType.
Variable leT : rel T.

Hypothesis leT_tr : transitive leT.

Lemma sorted_drop (s : seq T) m : sorted leT s -> sorted leT (drop m s).
Proof.
by elim: s m => //= a l ih [|n h] //; apply/ih/(path_sorted h).
Qed.

Lemma subseq_take (s : seq T) m : subseq (take m s) s.
Proof. by elim: s m => // a l ih [] //= n; rewrite eqxx. Qed.

Lemma sorted_take (s : seq T) m : sorted leT s -> sorted leT (take m s).
Proof.
move=> H; exact: (subseq_sorted leT_tr (subseq_take _ _) H).
Qed.

End Seqeqtype.

(******************** bigop.v ********************)
Section BigOp.

Import GRing.Theory.

Variable R : comRingType.
Variable T : eqType.

Open Scope ring_scope.

(*** This lemma is usefull to prove that \mu_x p = count_mem x s where
     s is the sequence of roots of polynomial p ***)
Lemma prod_seq_count (s : seq T) (F : T -> R) :
  \prod_(i <- s) F i =
  \prod_(i <- (undup s)) ((F i) ^+ (count (xpred1 i) s)).
Proof.
elim: s=> /= [|a l IHl]; first by rewrite !big_nil.
rewrite big_cons IHl.
set r:= if _ then _ else _.
have ->: \big[*%R/1]_(i <- r) (F i) ^+ ((a == i) + count (eq_op^~ i) l) =
         \big[*%R/1]_(i <- r) (F i) ^+ (a == i) *
         \big[*%R/1]_(i <- r) (F i) ^+ (count (eq_op^~ i) l).
  by rewrite -big_split /=; apply: eq_bigr=> i _; rewrite exprD.
have ->: \big[*%R/1]_(i <- r) (F i) ^+ (a == i) = F a.
  rewrite /r; case: ifP=>[|notal].
    rewrite -mem_undup=> aundl.
    rewrite (bigD1_seq _ aundl (undup_uniq l)) /= eqxx big1 ?mulr1 //.
    by move=> i /negbTE neqai; rewrite eq_sym neqai.
  rewrite big_cons eqxx big1_seq ?mulr1 // => i /= iundl.
  case: (eqVneq a i) => //= eqai.
  by rewrite eqai -mem_undup iundl in notal.
rewrite /r; case: ifP=> // /negbT notal.
rewrite big_cons.
have->: count (xpred1 a) l = 0%N.
  by apply/eqP; rewrite -leqn0 leqNgt -has_count has_pred1.
by rewrite mul1r.
Qed.

End BigOp.

(********************* matrix.v *********************)
Section Matrix.

Local Open Scope ring_scope.
Import GRing.Theory.

Section matrix_raw_type.

Variable T : Type.

Lemma row_thin_mx  p q (M : 'M_(p,0)) (N : 'M[T]_(p,q)) :
  row_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP=> [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

Lemma col_flat_mx p q (M : 'M[T]_(0, q)) (N : 'M_(p,q)) :
  col_mx M N = N.
Proof.
apply/matrixP=> i j; rewrite mxE; case: splitP => [|k H]; first by case.
by congr fun_of_matrix; exact: val_inj.
Qed.

End matrix_raw_type.

Section matrix_ringType.

Variable R : ringType.

Lemma mulmx_rsub m n p k (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p + k)) :
  A *m rsubmx B = (rsubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma mulmx_lsub m n p k (A : 'M[R]_(m, n)) (B : 'M[R]_(n, p + k)) :
  A *m lsubmx B = (lsubmx (A *m B)).
Proof.
by apply/matrixP=> i j; rewrite !mxE; apply: eq_bigr => l //= _; rewrite mxE.
Qed.

Lemma col_0mx m n (M : 'M[R]_(m, n)) : col_mx (0 :'M_(0%N, _)) M = M.
Proof.
apply/matrixP=> i j; rewrite !mxE.
case: splitP => [[] //|k eq_i_k]; congr (M _ _).
by apply: val_inj; rewrite /= eq_i_k.
Qed.

(* to be replaced by col1 and colE (once they are in mathcomp) *)
Lemma col_id_mulmx m n (M : 'M[R]_(m,n)) i :
  M *m col i 1%:M = col i M.
Proof.
apply/matrixP=> k l; rewrite !mxE.
rewrite (bigD1 i) // big1 /= ?addr0 ?mxE ?eqxx ?mulr1 // => j /negbTE neqji.
by rewrite !mxE neqji mulr0.
Qed.

(* to be replaced by row1 and rowE *)
Lemma row_id_mulmx m n (M : 'M[R]_(m,n)) i :
   row i 1%:M *m M = row i M.
Proof.
apply/matrixP=> k l; rewrite !mxE.
rewrite (bigD1 i) // big1 /= ?addr0 ?mxE ?eqxx ?mul1r // => j /negbTE Hj.
by rewrite !mxE eq_sym Hj mul0r.
Qed.

Lemma row'_col'_char_poly_mx m i (M : 'M[R]_m) :
  row' i (col' i (char_poly_mx M)) = char_poly_mx (row' i (col' i M)).
Proof.
apply/matrixP=> k l; rewrite !mxE.
suff ->: (lift i k == lift i l) = (k == l) => //.
by apply/inj_eq/lift_inj.
Qed.

Lemma exp_block_mx m n (A: 'M[R]_m.+1) (B : 'M_n.+1) k :
  (block_mx A 0 0 B) ^+ k = block_mx (A ^+ k) 0 0 (B ^+ k).
Proof.
elim: k=> [|k IHk].
  by rewrite !expr0 -scalar_mx_block.
rewrite !exprS IHk /GRing.mul /= (mulmx_block A 0 0 B (A ^+ k)).
by rewrite !mulmx0 !mul0mx !add0r !addr0.
Qed.

Lemma char_block_mx m n (A : 'M[R]_m) (B : 'M[R]_n) :
  char_poly_mx (block_mx A 0 0 B) =
  block_mx (char_poly_mx A) 0 0 (char_poly_mx B).
Proof.
apply/matrixP=> i j; rewrite !mxE.
case: splitP=> k Hk; rewrite !mxE; case: splitP=> l Hl; rewrite !mxE;
rewrite -!(inj_eq (@ord_inj _)) Hk Hl ?subr0 ?eqn_add2l //.
  by rewrite ltn_eqF // ltn_addr.
by rewrite gtn_eqF // ltn_addr.
Qed.

End matrix_ringType.

Section matrix_comUnitRingType.

Variable R : comUnitRingType.

Lemma invmx_block n1 n2  (Aul : 'M[R]_n1.+1) (Adr : 'M[R]_n2.+1) :
   (block_mx Aul 0 0 Adr) \in unitmx ->
  (block_mx Aul 0 0 Adr)^-1 = block_mx Aul^-1 0 0 Adr^-1.
Proof.
move=> Hu.
have Hu2: (block_mx Aul 0 0 Adr) \is a GRing.unit by [].
rewrite unitmxE det_ublock unitrM in Hu.
case/andP: Hu; rewrite -!unitmxE => HAul HAur.
have H: block_mx Aul 0 0 Adr * block_mx Aul^-1 0 0 Adr^-1 = 1.
  rewrite /GRing.mul /= (mulmx_block Aul _ _ _ Aul^-1) !mulmxV //.
  by rewrite !mul0mx !mulmx0 !add0r addr0 -scalar_mx_block.
by apply: (mulrI Hu2); rewrite H mulrV.
Qed.

End matrix_comUnitRingType.

End Matrix.

Section Poly.

Variable R : idomainType.
Import GRing.Theory.
Local Open Scope ring_scope.

(* use coprimep_XsubC2 *)
Lemma coprimep_factor (a b : R) : (b - a)%R \is a GRing.unit ->
   coprimep ('X - a%:P) ('X - b%:P).
Proof.
move=> Hab; apply/Bezout_coprimepP.
exists ((b - a)^-1%:P, -(b - a) ^-1%:P).
rewrite /= !mulrBr !mulNr opprK -!addrA (addrC (- _)) !addrA addrN.
by rewrite add0r -mulrBr -rmorphB -rmorphM mulVr // eqpxx.
Qed.

End Poly.

(****************************************************************************)
(****************************************************************************)
(************ left pseudo division, it is complement of polydiv. ************)
(****************************************************************************)
(****************************************************************************)
Import GRing.Theory.
Import Pdiv.Ring.
Import Pdiv.RingMonic.

Local Open Scope ring_scope.

Module RPdiv.

Section RingPseudoDivision.

Variable R : ringType.
Implicit Types d p q r : {poly R}.

Definition id_converse_def := (fun x : R => x : R^c).
Lemma add_id : additive id_converse_def.
Proof. by []. Qed.

HB.instance Definition _ := GRing.isAdditive.Build R R^c id_converse_def add_id.
Definition id_converse : {additive _ -> _} := id_converse_def.

Lemma expr_rev (x : R) k : (x : R^c) ^+ k = x ^+ k.
Proof. by elim:k=> // k IHk; rewrite exprS exprSr IHk. Qed.

Definition phi (p : {poly R}^c) := map_poly id_converse p.

Fact phi_is_rmorphism : multiplicative phi.
Proof.
split=> [p q|]; apply/polyP=> i; last by rewrite coef_map !coef1.
by rewrite coefMr coef_map coefM; apply: eq_bigr => j _; rewrite !coef_map.
Qed.

HB.instance Definition _ := GRing.Additive.copy phi phi.
HB.instance Definition _ := GRing.isMultiplicative.Build _ _ _ phi_is_rmorphism.

Definition phi_inv (p : {poly R^c}) :=
  map_poly (fun x : R^c => x : R) p : {poly R}^c.

Lemma phiK : cancel phi phi_inv.
Proof. by move=> p; rewrite /phi_inv -map_poly_comp_id0 // map_poly_id. Qed.

Lemma phi_invK : cancel phi_inv phi.
Proof. by move=> p; rewrite /phi -map_poly_comp_id0 // map_poly_id. Qed.

Lemma phi_bij : bijective phi.
Proof. by exists phi_inv; first exact: phiK; exact: phi_invK. Qed.

Lemma monic_map_inj (aR rR : ringType) (f : aR -> rR) (p : {poly aR}) :
  injective f -> f 0 = 0 -> f 1 = 1 -> map_poly f p \is monic = (p \is monic).
Proof.
move=> inj_f eq_f00 eq_f11; rewrite !monicE lead_coef_map_inj ?rmorph0 //.
by rewrite -eq_f11 inj_eq.
Qed.

Definition redivp_l (p q : {poly R}) : nat * {poly R} * {poly R} :=
  let:(d,q,p) := redivp (phi p) (phi q) in
  (d, phi_inv q, phi_inv p).

Definition rdivp_l p q := (redivp_l p q).1.2.
Definition rmodp_l p q := (redivp_l p q).2.
Definition rscalp_l p q := (redivp_l p q).1.1.
Definition rdvdp_l p q := rmodp_l q p == 0.
Definition rmultp_l := [rel m d | rdvdp_l d m].

Lemma ltn_rmodp_l p q : (size (rmodp_l p q) < size q) = (q != 0).
Proof.
have := ltn_rmodp (phi p) (phi q).
rewrite -(rmorph0 phi) (inj_eq (can_inj phiK)) => <-.
rewrite /rmodp_l /redivp_l /rmodp; case: (redivp _ _)=> [[k q'] r'] /=.
by rewrite !size_map_inj_poly.
Qed.

End RingPseudoDivision.

Module mon.

Section MonicDivisor.

Variable R : ringType.
Implicit Types p q r : {poly R}.

Variable d : {poly R}.
Hypothesis mond : d \is monic.

Lemma rdivp_l_eq p :
  p = d * (rdivp_l p d) + (rmodp_l p d).
Proof.
have mon_phi_d: phi d \is monic by rewrite monic_map_inj.
apply:(can_inj (@phiK R)); rewrite {1}[phi p](rdivp_eq mon_phi_d) rmorphD.
rewrite rmorphM /rdivp_l /rmodp_l /redivp_l /rdivp /rmodp.
by case: (redivp _ _)=> [[k q'] r'] /=; rewrite !phi_invK.
Qed.

End MonicDivisor.

End mon.

End RPdiv.


Section prelude.
Variable R : comRingType.

Let lreg := GRing.lreg.
Let rreg := GRing.rreg.

Lemma monic_lreg (p : {poly R}) : p \is monic -> lreg p.
Proof. by rewrite monicE=> /eqP lp1; apply/lreg_lead; rewrite lp1; apply/lreg1. Qed.

Lemma monic_rreg (p : {poly R}) : p \is monic -> rreg p.
Proof. by rewrite monicE=> /eqP lp1; apply/rreg_lead; rewrite lp1; apply/rreg1. Qed.

Lemma lregMl (a b: R) : lreg (a * b) -> lreg b.
Proof. by move=> rab c c' eq_bc;  apply/rab; rewrite -!mulrA eq_bc. Qed.

Lemma rregMr (a b: R) : rreg (a * b) -> rreg a.
Proof. by move=> rab c c' eq_ca;  apply/rab; rewrite !mulrA eq_ca. Qed.

End prelude.

(******************************************************************************)
(*        Ideals with respect to a list of elemets                            *)
(*  ideal L p     : p is in the ideal generated by L                          *)
(******************************************************************************)

Section Ideal.

Variable R : ringType.
Variable n : nat.

Implicit Types x y : R.

Variable L : seq R.

Definition ideal x : Prop :=
  exists (t : (size L).-tuple _), x = \sum_(i < size L) t`_i * L`_i.

Lemma ideal0 : ideal 0.
Proof.
exists (nseq_tuple _ 0).
rewrite big1 // => i /=.
by rewrite nth_nseq if_same mul0r.
Qed.

Lemma idealN x : ideal x -> ideal (- x).
Proof.
case=>t ->.
exists [tuple - t`_i | i < size L] => //.
rewrite -sumrN; apply: eq_bigr => i _ /=.
by rewrite (nth_map i) ?size_enum_ord // nth_enum_ord // -mulNr.
Qed.

Lemma idealD x y : ideal x -> ideal y -> ideal (x + y).
Proof.
move=> [t1 ->][t2 ->].
exists [tuple (t1`_i + t2`_i) | i < size L] => //.
rewrite -big_split; apply: eq_bigr => i _ /=.
by rewrite (nth_map i) ?size_enum_ord // nth_enum_ord // mulrDl.
Qed.

Lemma idealB x y : ideal x -> ideal y -> ideal (x - y).
Proof. by move=> Ix Iy; apply: idealD => //; apply: idealN. Qed.

Lemma idealM x y : ideal y -> ideal (x * y).
Proof.
case=>t ->.
exists [tuple (x * t`_i) | i < size L] => //.
rewrite mulr_sumr; apply: eq_bigr => i _ /=.
by rewrite (nth_map i) ?size_enum_ord //  nth_enum_ord // mulrA.
Qed.

Lemma ideal_mem x : x \in L -> ideal x.
Proof.
move=> Ix.
have Hp : (index x L < size L)%nat by rewrite index_mem.
pose j := Ordinal Hp.
exists [tuple if i == j then 1 else 0 | i < size L].
rewrite (bigD1 j) //= big1 /= => [|[i /= Hi] /= iDj]; last first.
- rewrite (nth_map j) ?size_enum_ord //=.
  case: ifP; last by rewrite mul0r.
  move/eqP/val_eqP; rewrite /= nth_enum_ord => //= HH.
  by case/eqP: iDj; apply/val_eqP => /=.
rewrite (nth_map j) ?size_enum_ord //=.
case: ifP; last first.
- by move/eqP/val_eqP; rewrite /= nth_enum_ord // eqxx.
by rewrite nth_index // addr0 mul1r.
Qed.

End Ideal.

Lemma ideal_consr (R : ringType) (l : seq R) x y :
  ideal l x -> ideal (y :: l) x.
Proof.
case=> t ->; exists [tuple of 0 :: t] => /=.
by rewrite big_ord_recl /= mul0r add0r.
Qed.

Lemma ideal_consl (R : ringType) (l : seq R) x y :
  ideal l x -> ideal (x :: l) y -> ideal l y.
Proof.
case=> [t1] ->; case=> /= t2 ->.
exists [tuple (t2`_0 * t1`_i + t2`_(fintype.lift ord0 i))| i < size l].
rewrite big_ord_recl [X in _ * X + _ = _]/=.
rewrite mulr_sumr -big_split.
apply: eq_bigr => i _ /=.
rewrite (nth_map i); last by rewrite size_enum_ord ltn_ord.
rewrite nth_enum_ord; last by apply: ltn_ord.
by rewrite mulrDl mulrA.
Qed.

Lemma idealZ (R1 : ringType) (R2 : lalgType R1) (L : seq R2) a x : 
  ideal L x -> ideal L (a *: x).
Proof.
case=>t ->.
exists [tuple (a *: t`_i) | i < size L] => //.
rewrite scaler_sumr; apply: eq_bigr => i _ /=.
by rewrite (nth_map i) ?size_enum_ord // nth_enum_ord // scalerAl.
Qed.


(****************************************************************************)
(****************************************************************************)
(****************************************************************************)
(****************************************************************************)
