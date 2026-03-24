(* The CoqEAL library https://github.com/rocq-community/coqeal
is composed of two main parts
* The theory/ subdirectory contains linear algebra results.
  This can be seen as an extension of the MathComp library.
* The refinements/ library contain tools to perform parametricity
  proofs, typically to refine results from a proof-oridented type
  (for instance MathComp matrices) to a type more amenable for
  computations (e.g. matrices as lists of lists).
The current tutorial only covers the second part, through the
example of matrices. *)

(* N.B.: While CoqEAL is still maintained, it is no longer actively
developped. The future of parametricity proofs in Rocq is probably Trocq:
https://rocq-community.org/trocq/index.html#/quick-start
but it still lacks a few features from Coqeal, including the automatic
parametricity refinement for inductive types and the library with matrices,
some numbers,... *)

(* This has been tested with
* Rocq 9.0
* rocq-elpi 3.1.0 (on elpi 3.1.0)
* MathComp 2.4.0
* MathComp reals 1.13.0 (part of MathComp Analysis)
* CoqEAL 2.1.0 *)
From mathcomp Require Import all_ssreflect order ssralg ssrnum matrix reals.
From CoqEAL Require Import hrel param refinements trivial_seq.
From CoqEAL Require Import seqmx seqmx_complements.

Unset SsrOldRewriteGoalsOrder.  (* remove the line when requiring MathComp >= 2.6 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory GRing.Theory Num.Theory.
Import Refinements.Op.

Local Open Scope ring_scope.

(* The following is essentially generalizing material from the matrix.v file
from MathComp and the seqmx.v file of CoqEAL.
One can jump to "Section Tutorial." below,
for the actual start of the tutorial. *)

(* Currently, the matrix addition of MathComp requires a nmodType (that
requirement could be lowered now that we have magma types in MC)
We can't equip floats with such a structure (no addition associativity for
instance), so we redefine matrix addition for now. *)
Definition addmx (R : Type) (Radd : R -> R -> R) (m n : nat) :=
  @map2_mx R R R Radd m n.

(* Currently, the matrix multiplication of MathComp requires a semiRingType.
We can't equip floats with such a structure (no addition associativity for
instance), so we redefine matrix multiplication for now. *)
Definition mulmx (R : Type) (R0 : R) (Radd Rmul : R -> R -> R) (m n p : nat)
    (A : 'M_(m, n)) (B : 'M_(n, p)) :=
  (\matrix_(i, k)
     (foldl (fun r j => Radd (Rmul (A i j) (B j k)) r) R0 (ord_enum n)))%R.

Section Rseqmx_add_mul.

Variables (R : Type) (R0 : R) (Radd Rmul : R -> R -> R).

#[local] Instance zeroR : zero_of R := R0.
#[local] Instance addR : add_of R := Radd.
#[local] Instance mulR : mul_of R := Rmul.

#[local] Instance Rseqmx_add m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (Rseqmx (R:=R) rm rn ==> Rseqmx rm rn ==> Rseqmx rm rn)
    (@addmx R Radd m1 n1) +%C.
Proof.
rewrite refinesE=> _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
constructor=> [|i ltim|i j]; rewrite [(_ + _)%C]zipwithE.
- by rewrite size_map size1_zip h1 ?h'1.
- by rewrite (nth_map ([::], [::])) ?nth_zip ?zipwithE ?size_map ?size1_zip /=
             ?h1 ?h'1 ?h2 ?h'2 ?ltim.
- by rewrite (nth_map ([::], [::])) ?nth_zip /= ?size1_zip ?h1 ?h'1
             -?(nat_R_eq rm) ?ltn_ord // mxE h3 h'3 zipwithE
             -[[seq _ | _ <- _]](mkseq_nth 0%C) nth_mkseq /=
             ?(nth_map (0%C, 0%C)) ?nth_zip ?size_map /= ?size1_zip ?h2 ?h'2
             -?(nat_R_eq rm) -?(nat_R_eq rn) ?ltn_ord.
Qed.

#[local] Instance Rseqmx_mul m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
    p1 p2 (rp : nat_R p1 p2) :
  refines (Rseqmx (R:=R) rm rn ==> Rseqmx rn rp ==> Rseqmx rm rp)
    (@mulmx R R0 Radd Rmul m1 n1 p1) (@hmul_op _ _ _  m2 n2 p2).
Proof.
case: rn => [|k1 k2 rk] /[!refinesE] _ _ [M sM h1 h2 h3] _ _ [N sN h'1 h'2 h'3].
  constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx /seqmx0.
  - by rewrite size_nseq.
  - by rewrite nth_nseq h1 ltim size_nseq.
  - by rewrite nth_nseq h1 -(nat_R_eq rm) ltn_ord nth_nseq -(nat_R_eq rp)
               ltn_ord mxE.
constructor=> [|i ltim|i j]; rewrite /hmul_op /mul_seqmx.
- by rewrite size_map.
- by rewrite (nth_map [::]) ?h1 // size_map /trseqmx /= size_fold ?h'1.
rewrite (nth_map [::]) ?h1 -?(nat_R_eq rm) // (nth_map [::]) /trseqmx
        ?size_fold ?h'1 ?h'2 // -?(nat_R_eq rp) //.
set F := fun z x y => _.
have -> : forall s1 s2 (t : R), foldl2 F t s1 s2
    = foldl (fun r k => Radd (Rmul (nth R0 s1 k) (nth R0 s2 k)) r)
        t (iota 0 (minn (size s1) (size s2))).
  elim=> [s2 t|t1 s1 IHs s2 t]; first by rewrite min0n.
  case: s2 => [|t2 s2]; first by rewrite minn0.
  rewrite /= IHs minSS /= -[1%N]/(1 + 0)%N iotaDl -[Radd _ _]/(F t t1 t2).
  by elim: iota (F t t1 t2) => [//|k kl IH /=] t'; rewrite IH; congr foldl.
set F' := fun _ _ => _.
rewrite size_nth_fold ?h'1 ?h2 -?(nat_R_eq rm) //
        ?(nat_R_eq rp) // minnn mxE -(nat_R_eq rk).
rewrite -val_ord_enum /zero_op /zeroR.
elim: ord_enum R0 => [//|k kl IH /=] r; rewrite IH; congr foldl.
by rewrite /F' /= h3 h'3 nth_fold ?h'1 ?(nat_R_eq rp)// -(nat_R_eq rk).
Qed.

Section RseqmxC_add_mul.

Context (C : Type) (rAC : R -> C -> Type).
Context `{zero_of C, add_of C, mul_of C}.
Context `{!refines rAC R0 0%C}.
Context `{!refines (rAC ==> rAC ==> rAC) Radd +%C}.
Context `{!refines (rAC ==> rAC ==> rAC) Rmul *%C}.

#[local] Notation RseqmxC := (RseqmxC rAC).

#[export] Instance RseqmxC_add m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) :
  refines (RseqmxC rm rn ==> RseqmxC rm rn ==> RseqmxC rm rn)
    (@addmx R Radd m1 n1) +%C.
Proof. param_comp add_seqmx_R. Qed.

#[export] Instance refine_add_seqmx m n :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx m) (nat_Rxx n)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx n))
    (@addmx R Radd m n) +%C.
Proof. exact: RseqmxC_add. Qed.

#[export] Instance RseqmxC_mul m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2)
       p1 p2 (rp : nat_R p1 p2) :
  refines (RseqmxC rm rn ==> RseqmxC rn rp ==> RseqmxC rm rp)
    (@mulmx R R0 Radd Rmul m1 n1 p1) (@hmul_op _ _ _  m2 n2 p2).
Proof. param_comp mul_seqmx_R. Unshelve. all: exact: nat_Rxx. Qed.

#[export] Instance refine_mul_seqmx m n p :
  refines (RseqmxC (nat_Rxx m) (nat_Rxx n) ==> RseqmxC (nat_Rxx n) (nat_Rxx p)
                   ==> RseqmxC (nat_Rxx m) (nat_Rxx p))
    (@mulmx R R0 Radd Rmul m n p) (@hmul_op _ _ _  m n p).
Proof. exact: RseqmxC_mul. Qed.

End RseqmxC_add_mul.

End Rseqmx_add_mul.

(* a small lemma missing in CoqEAL *)
Lemma eq_seqmx_eq (T : eqType) :
  @eq_seqmx _ eqtype.eq_op =2 @eqtype.eq_op (@seqmx T).
Proof.
elim=> [//| a1 A1 IH] [//| a2 A2] /=; congr andb; last exact: IH.
elim: a1 a2 => [//| c1 a1 {}IH] [//| c2 a2]; congr andb; exact: IH.
Qed.

(* The tutorial actually starts here *)
Section Tutorial.

(* We want to do a refinement proof of lemma mat_vec_mul_mixed_error in
https://github.com/VeriNum/LAProof/blob/main/accuracy_proofs/gemv_acc.v *)
Section MatVecMul.

(* Assume some type for floats (for instance from libvalidsdp) *)
Variables F : Type.
(* with 0, addition and multiplication *)
Variables (F0 : F) (Fadd Fmul : F -> F -> F).
(* and an injection into real numbers *)
Variables (R : realType) (F2R : F -> R).

(* Assume some bounds (actual values don't matter much for now) *)
Variables (g : nat -> R) (g1 : nat -> nat -> R).

#[local] Notation MF2R := (map_mx F2R).
#[local] Notation Fmulmx := (mulmx F0 Fadd Fmul).
#[local] Notation Raddmx := (addmx +%R).
#[local] Notation Rmulmx := (mulmx 0 +%R *%R).

(* First, we prove our lemma on the nice proof-oriented type 'M[F] *)
Lemma mx_vec_mul_mixed_error m n (A : 'M[F]_(m, n)) (v : 'cV_n) :
  exists (E : 'M[R]_(m, n)) (eta : 'cV[R]_m),
    [/\ MF2R (Fmulmx A v) = Raddmx (Rmulmx (Raddmx (MF2R A) E) (MF2R v)) eta
      , (forall i j, `|E i j| <= g n * `|F2R (A i j)|)
      & (forall i, `|eta i ord0| <= g1 n n)].
Admitted.  (* actual proof is outside the scope of the tutorial *)

(* Now we will derive the lemma on matrices as lists of lists (@seqmx F) *)

#[local] Notation sMF2R := (map_seqmx F2R).

(* CoqEAL highly relies on Rocq typeclasses to automate proofs.
This comes with all the caveat of typeclasses in Rocq: any new instance
can make everything blow up, debugging can be very painful. *)

(* So we need to declare a few instances, on both F and R: *)
#[local] Instance zeroF : zero_of F := F0.
#[local] Instance addF : add_of F := Fadd.
#[local] Instance mulF : mul_of F := Fmul.
#[local] Instance specF : spec_of F F := spec_id.

#[local] Instance zeroR' : zero_of R := 0.
#[local] Instance addR' : add_of R := +%R.
#[local] Instance mulR' : mul_of R := *%R.
#[local] Instance specR' : spec_of R R := spec_id.

(* We also reinstantiate some lemmas that we'll use in the proof *)
Existing Instance implem_ord.
Existing Instance Rseqmx_eq.
Existing Instance Rseqmx_add.
Existing Instance Rseqmx_mul.

(* Then, we actually derive the lemma on seqmx *)
Lemma seqmx_vec_mul_mixed_error m n (A v : @seqmx F) :
  size A = m -> (forall i, (i < m)%N -> size (nth [::] A i) = n) ->
  size v = n -> (forall i, (i < n)%N -> size (nth [::] v i) = 1) ->
  exists (E eta : @seqmx R),
    [/\ sMF2R (@mul_seqmx _ _ _ _ m n 1 A v)
        = add_seqmx (@mul_seqmx _ _ _ _ m n 1 (add_seqmx (sMF2R A) E) (sMF2R v))
            eta
      , (forall i j, `|spec_seqmx m n E i j : R|
          <= g n * `|F2R (spec_seqmx m n A i j)|)
      , (forall i, `|spec_seqmx m 1 eta i ord0 : R| <= g1 n n)
      , size E = m /\ (forall i, (i < m)%N -> size (nth [::] E i) = n)
      & size eta = m /\ (forall i, (i < m)%N -> size (nth [::] eta i) = 1)].
Proof.
move=> srA scA srv scv.
(* First define the specifications of matrices A and v *)
set sA : 'M[F]_(m, n) := spec_seqmx m n A.
set sv : 'cV[F]_n := spec_seqmx n 1 v.
(* which enables to use our previous lemma *)
have [E [eta [/eqP mAv Eb etab]]] := mx_vec_mul_mixed_error sA sv.
(* we define the implementations of the resulting E and eta *)
set iE := seqmx_of_fun E.
set ieta := seqmx_of_fun eta.
(* we then prove that each specification is refined by the original seqmx
Here:
* [Rseqmx rm rn A1 A2] means that the matrices (A1 : 'M[F]_(m1, n1))
  and (A2 : @seqmx F) refine each other (i.e., have the same size and content)
  where [rm : nat_R m1 m2] and [rn : nat_R n1 n2] are refinements between
  natural numbers (which amounts to equalities m1 = m2 and n1 = n2),
  here we always use [nat_Rxx : forall n, nat_R n n].
* [refines] is an identity used as a tag to trigger typeclass search.
  It is typically removed with [refinesE] and introduced with [refinesP]. *)
have rA : refines (Rseqmx (nat_Rxx m) (nat_Rxx n)) sA A.
  rewrite refinesE; apply/Rseqmx_spec_seqmx/andP; split; [exact/eqP|].
  by apply/(all_nthP [::]); rewrite srA => ? ?; apply/eqP/scA.
have rv : refines (Rseqmx (nat_Rxx n) (nat_Rxx 1)) sv v.
  rewrite refinesE; apply/Rseqmx_spec_seqmx/andP; split; [exact/eqP|].
  by apply/(all_nthP [::]); rewrite srv => ? ?; apply/eqP/scv.
(* similarly, each implementation refines its original matrix *)
have rE : refines (Rseqmx (nat_Rxx m) (nat_Rxx n)) E iE.
  have -> : E = \matrix_(i, j) E i j by apply/matrixP => ? ?; rewrite mxE.
  by apply/Rseqmx_seqmx_of_fun; rewrite refinesE => -[? ? ? <-] [? ? ? <-].
have reta : refines (Rseqmx (nat_Rxx m) (nat_Rxx 1)) eta ieta.
  have -> : eta = \matrix_(i, j) eta i j by apply/matrixP => ? ?; rewrite mxE.
  by apply/Rseqmx_seqmx_of_fun; rewrite refinesE => -[? ? ? <-] [? ? ? <-].
exists iE; exists ieta; split.
- (* we want to prove that this equality is [mAv] modulo refinement *)
  apply/eqP/esym; rewrite -eq_seqmx_eq -mAv.
  (* we first need to prove that sMF2R refines MF2R *)
  have rmm m' (rm' : nat_R m' m') n' (rn : nat_R n' n') :
      refines (Rseqmx rm' rn ==> Rseqmx rm' rn) MF2R sMF2R.
    by apply: (refines_apply (Rseqmx_map_seqmx _ _)); rewrite refinesE.
  (* finally, we use [refinesP] to trigger the typeclass search that will map
     equality and each addition and multiplication,
     according to known instances *)
  exact: refinesP.
- move=> i j; have <-// : E = (spec_seqmx m n iE).
  exact/refinesP/(refines_apply (Rseqmx_spec_l _ _ _)).
- move=> i; have <-// : eta = (spec_seqmx m 1 ieta).
  exact/refinesP/(refines_apply (Rseqmx_spec_l _ _ _)).
- by case: (refinesP rE).
- by case: (refinesP reta).
Qed.

(* We just used [Rseqmx] to refine ['M[R]_(m, n)] by [@seqmx R]
   but we could similarly use [RseqmxC] to directly refine ['M[R]_(m, n)]
   by some [@seqmx R'] were [R'] could be some refinement of [R]. *)
About RseqmxC.

End MatVecMul.

(* Finally, a nice capability offered by CoqEAL (and more precisely
Elpi derive.param2 (and previously the paramcoq plugin) on which it is based)
is to automatically derive refinement proofs for inductive types and programs,
assuming refinements for their parameters. *)
Section Derive2.

(* We define some program doing stuffs on matrices.
The type of matrices is parameterized *)
Section Prog.
(* Assume some type of matrices *)
Variable (M : nat -> nat -> Type).
(* with a boolean equality *)
Variable (Meq : forall m n, M m n -> M m n -> bool).
(* and addition *)
Variable (Madd : forall m n, M m n -> M m n -> M m n).

(* some program, computing some arbirary stuff for the sake of the example *)
Fixpoint prog m n (A B : M m n) k :=
  if k isn't k'.+1 then B else prog A (Madd A B) k'.
End Prog.

(* Once the program defined, we can automatically derive its refinement proof *)
Elpi derive.param2 prog.
(* This defines a new lemma [prog_R] *)
About prog_R.

Section TestProg.

(* Assume some type of coefficients (with some zero and addition) *)
Context R (zR : zero_of R) (Radd : add_of R).

(* Using the basic blocks from CoqEAL
(here refinement of matrix addition [Rseqmx_add]), the derived lemma [prog_R]
immediatly gives that [prog (addmx Radd)] on MathComp matrices
is refined by [prog (fun _ _ => @add_seqmx R _)] on [@seqmx R]. *)
Check @prog_R (matrix R) (@hseqmx R) (@Rseqmx R _) _ _
  (fun m1 m2 (rm : nat_R m1 m2) n1 n2 (rn : nat_R n1 n2) =>
     refinesP (Rseqmx_add zR Radd rm rn)).

End TestProg.

End Derive2.

End Tutorial.
