Require Import ssreflect ssrnat ssrfun fintype finfun finset eqtype ssrbool seq binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section StrictMonotoneFiniteFunctions.

Record delta_plus : Type := DeltaPlus {
  source_card : nat;
  bump_seq : seq nat
}.

Fixpoint fun_of_bump_seq (l : seq nat) :=
  match l with
    |[::] => id
    | a :: tl => 
      (fun_of_bump_seq tl) \o (bump a)
  end.


Lemma fun_of_bump_seqP n l (i : 'I_n) : fun_of_bump_seq l i < size l + n.
Proof.
elim: l => [| a tl ihl] //= in n i *.
have hbump: bump a i < n.+1.
  apply: (@leq_ltn_trans i.+1); last by rewrite ltnS.
  by rewrite /bump; case: (leqP a i).
by apply: leq_trans (ihl _ (Ordinal hbump)) _; rewrite addnS.
Qed.

Definition ffun_of_bump_seq n l :=
  [ffun i => Ordinal (@fun_of_bump_seqP n l i)].

Definition epsilon i := fun_of_bump_seq [:: i].

Lemma epsilonE i j : epsilon i j = bump i j :> nat. Proof. by []. Qed.

Lemma leqmono_incr f x y : {mono f : i j / i <= j} -> x < y -> f x < f y.
Proof.
by move=> hf hxy; apply: contraLR hxy; rewrite -!leqNgt; rewrite hf.
Qed.

Lemma leqmono_subid f x : {mono f : i j / i <= j} -> x <= f x.
Proof.
move=> fmon; elim: x => [| x ihx]; first by rewrite leq0n.
by apply: leq_ltn_trans ihx _; apply: leqmono_incr.
Qed.

Lemma bump_seq_of_ffunP n (f : 'I_n.+1 -> nat) : 
  {mono f : i j / i <= j} -> 
  exists2 g : seq nat, size g = (f ord_max) - n &  
  forall x : 'I_n.+1, fun_of_bump_seq g x = f x :> nat.
Proof.
elim: n f => [| n ihn] f fmon //=.
  rewrite subn0.
  exists (iota 0 (f ord_max)) => [|x]; first by rewrite size_iota.
  have {x}-> : x = ord0 by apply/ord_inj; case: x => [[|k]].
  have /= -> : ord_max = ord0 :> 'I_1 by apply: val_inj.
  suff h x k : k <= x -> fun_of_bump_seq  (iota k (f ord0)) x = x + (f ord0).
    by rewrite h.
  elim: (f ord0) x k => [x |n ihn x k hx]; first by [].
  rewrite /=  ihn; first by rewrite /bump hx -addnA addnCA.
  by apply: leq_ltn_trans (hx) _; rewrite /bump hx /= ltnSn.
have [f0_eq0|f0_gt0] := posnP (f ord0).
  pose g (i : 'I_n.+1) := (f (lift ord0 i)).-1.
  have gmon : {mono g : i j / i <= j >-> i <= j}.
    move=> x y /=; rewrite /g.
    have -> : (x <= y) = (lift ord0 x <= lift ord0 y).
      by rewrite /= /bump !leq0n leq_add2l.
    rewrite -fmon.
    have /prednK {2}<-: f (lift ord0 x) > 0 .
Admitted.



(* Fixpoint fun_of_bump_seq (n : nat) (l : seq nat) := *)
(*   match l with *)
(*     |[::] => id *)
(*     | a :: tl =>  *)
(*       (fun_of_bump_seq n.+1 tl) \o (bump a) *)
(*   end. *)


(* Lemma fun_of_bump_seqP n l (i : 'I_n) : fun_of_bump_seq n l i < size l + n. *)
(* Proof. *)
(* elim: l => [| a tl ihl] //= in n i *. *)
(* have hbump: bump a i < n.+1. *)
(*   apply: (@leq_ltn_trans i.+1); last by rewrite ltnS. *)
(*   by rewrite /bump; case: (leqP a i). *)
(* by apply: leq_trans (ihl _ (Ordinal hbump)) _; rewrite addnS. *)
(* Qed. *)

(* Definition ffun_of_bump_seq n l := *)
(*   [ffun i => Ordinal (@fun_of_bump_seqP n l i)]. *)

(* Definition epsilon n i := fun_of_bump_seq n [:: i]. *)

(* Lemma epsilonE n i j : epsilon n i j = bump i j :> nat. Proof. by []. Qed. *)


(* Lemma bump_seq_of_ffunP n (f : 'I_n.+1 -> nat) :  *)
(*   {mono f : i j / i <= j} ->  *)
(*   exists2 g : seq nat, size g = (f ord_max) - n &   *)
(*   forall x : 'I_n.+1, fun_of_bump_seq n.+1 g x = f x :> nat. *)
(* Proof. *)
(* elim: n f => [| n ihn] f hmon //=. *)
(*   rewrite subn0. *)
(*   exists (rev (iota 0 (f ord_max))) => [|x]; first by rewrite size_rev size_iota. *)
(*   have {x}-> : x = ord0 by apply/ord_inj; case: x => [[|k]]. *)
(*   have -> : ord_max = ord0 :> 'I_1 by apply: val_inj. *)
(*   elim: (f ord0) => [|n ihn]; first by []. *)
(*   rewrite -{1}(addn1 n) iota_add add0n rev_cat /= /bump. *)
(*   case: n ihn. *)
(* Search _ (_.+1 = _ + 1).   *)
(* rewrite -addSn. (iota_add 0 1 n). *)
(* Search _ iota. *)
(*   rewrite /bump leqnn addn0. *)
(* Search _ bump. *)
(* Search _ iota. *)
  
(* About bumpC. *)
(*   have [f0_eq0|f0_gt0] := posnP (f ord0). *)
(*   - exists [::] => /= [|x]. *)
(*       by rewrite subn0 -[LHS]f0_eq0; apply/f_equal/f_equal/val_inj. *)
(*     suff -> : x = ord0 by rewrite f0_eq0. *)

(* (* bullets are screwed up : if the tactic fails, nothing happens. *) *)
(*   exists [:: nat_of_ord (f ord0)] => /=.  *)
(*     rewrite subn0.  *)
(*  by apply: ord_inj; rewrite f0_eq0. *)
    

(*     have -> : i = ord0 :> 'I_1. *)
(* Set Printing All. rewrite /= in f0_eq0. Check (@ord0 O). *)
(* About ord_inj.         *)

(*   by exists (nseq m 0) => [|[//]]; rewrite size_nseq. *)

(* Lemma bump_seq_of_ffunP n m (f : 'I_n -> 'I_(n + m)) :  *)
(*   {mono f : i j / i <= j} ->  *)

(*   exists2 g : seq nat, size g = m &   *)
(*   forall x : 'I_n, fun_of_bump_seq n g x = f x :> nat. *)
(* Proof. *)
(* elim: n f => [| [|n] ihn] f hm //=. *)
(* (*-*) by exists (nseq m 0) => [|[//]]; rewrite size_nseq. *)
(* (*-*) have [f0_eq0|f0_gt0] := posnP (f ord0). *)
(*         exists [::]. *)
(*   pose h (i : 'I_n) :=  @unlift (n + m).+1 ord0 (f (lift ord0 i)) : option 'I_(n + m). *)

(*   have [|g Hsg Hg] := @ihn m.+1 (fun i : 'I_n => inord (f (lift ord0 i))). *)
(*     move=> i j /=; rewrite addnS in f hm f0_eq0 *. *)
(*     by rewrite !inord_val hm. *)
(* Print bump. *)
(*   exists g. *)
(* Admitted. *)

End  StrictMonotoneFiniteFunctions.










Section SimplexExperience.

Fixpoint simplex n : seq (seq (seq nat)) :=
  if n is n'.+1 then
    let p := simplex n' in
    let fix aux prec r : seq (seq (seq nat)) :=
        let new := map (rcons^~ n') prec in
        if r is x :: s then (x ++ new) :: (aux x s) else [::new]
    in aux [::[::]] p
  else [::].

Lemma nth_simplex0 n : nth [::] (simplex n) 0 = map (nseq 1) (iota 0 n).
Proof.
elim: n => [|n IHn] //; rewrite -addn1 iota_add add0n addn1 /=.
by rewrite map_cat -!IHn; case: (simplex n).
Qed.

Lemma nth_simplexS n i : (nth [::] (simplex n.+1) i.+1) =
  (nth [::] (simplex n) i.+1) ++
  (map (rcons^~ n) (nth [::] (simplex n) i)).
Proof.
rewrite /=; set aux := (X in if (X _ _) is _ :: _ then _ else _).
by elim: (simplex n) i => [|x [|y s] //= IHs] [|i] /=.
Qed.

Lemma size_nth_simplex n i : size (nth [::] (simplex n) i) = 'C(n, i.+1).
Proof.
elim: n => [|n IHn] in i *; first by rewrite nth_default //= bin0n.
case: i => [|i]; last by rewrite nth_simplexS size_cat size_map !IHn.
by rewrite nth_simplex0 size_map size_iota bin1.
Qed.

Eval compute in simplex 4.

End  SimplexExperience.