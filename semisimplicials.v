Require Import ssreflect ssrnat ssrfun fintype finfun finset eqtype ssrbool seq binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section StrictMonotoneFiniteFunctions.

Record delta_plus : Type := DeltaPlus {
  source_card : nat;
  bump_seq : seq nat
}.

Fixpoint fun_of_bump_seq (n : nat) (l : seq nat) :=
  match l with
    |[::] => id
    | a :: tl => 
      (fun_of_bump_seq n.+1 tl) \o (bump a)
  end.


Lemma fun_of_bump_seqP n l (i : 'I_n) : fun_of_bump_seq n l i < size l + n.
Proof.
elim: l => [| a tl ihl] //= in n i *.
have hbump: bump a i < n.+1.
  apply: (@leq_ltn_trans i.+1); last by rewrite ltnS.
  by rewrite /bump; case: (leqP a i).
by apply: leq_trans (ihl _ (Ordinal hbump)) _; rewrite addnS.
Qed.

Definition ffun_of_bump_seq n l :=
  [ffun i => Ordinal (@fun_of_bump_seqP n l i)].

Definition epsilon n i := fun_of_bump_seq n [:: i].

Lemma epsilonE n i j : epsilon n i j = bump i j :> nat. Proof. by []. Qed.

Lemma bump_seq_of_ffunP n m (f : 'I_n -> 'I_(m + n)) : 
  {mono f : i j / i <= j} -> 
  exists2 g : seq nat, size g = m &  
  forall x : 'I_n, fun_of_bump_seq n g x = f x :> nat.
Proof.
elim: n m f => [| n ihn] m f hm //=.
  by exists (nseq m 0) => [|[//]]; rewrite size_nseq.
have [f0_eq0|f0_gt0] := posnP (f ord0).
  have [|g Hsg Hg] := @ihn m.+1 (fun i : 'I_n => inord (f (lift ord0 i))).
    move=> i j /=.
    rewrite addnS in f hm f0_eq0 *.
    by rewrite !inord_val hm.
  exists g.
Admitted.

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