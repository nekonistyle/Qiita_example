From mathcomp Require Import all_ssreflect.

Require Import Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)
Section Seq.
  Variable (T:Type).

  Function mkallrel (R:rel T) (s:seq T) {measure size s} :=
    if s is x :: s' then x :: mkallrel R (filter (R x) s') else [::].
  Proof.
    move => R s x s' _ /=. apply /leP.
      by rewrite size_filter ltnS count_size.
  Defined.

  Lemma my_mkallrel_ind R (P:seq T -> Prop) :
    P [::] ->
    (forall x s, P (filter (R x) s) -> P (x :: s)) ->
    forall s, P s.
  Proof.
    move => Hnil Hcons s.
    have [n] := ubnP (size s).
    elim : n s =>[|n IHn][|x s]//=. rewrite ltnS => Hsn.
    apply /Hcons /IHn. apply /leq_ltn_trans : Hsn.
      by rewrite size_filter count_size.
  Qed.

  Lemma all_filter p (s:seq T) : all p s -> forall q, all p (filter q s).
  Proof.
    elim : s =>[|x s IH]//= /andP[px Hps] q.
      by case : ifP; rewrite /= (IH Hps) ?px.
  Qed.

  Lemma all_mkallrel P (R:rel T) s : all P s -> all P (mkallrel R s).
  Proof.
    move : s. apply : my_mkallrel_ind =>[|x s IH]//= /andP[].
    rewrite mkallrel_equation =>/=->/= HPs. by apply /IH /all_filter.
  Qed.
End Seq.

Section EqSeq.
  Variable (T:eqType).

  Lemma mkallrel_subseq R (s:seq T) :
    subseq (mkallrel R s) s.
  Proof.
    have [n] := ubnP (size s).
    elim : n s =>[|n IHn][|x s]//=. rewrite ltnS => Hsn.
    rewrite mkallrel_equation eq_refl.
    apply /subseq_trans/IHn : (@filter_subseq _ (R x) s).
    rewrite size_filter. apply /leq_ltn_trans : Hsn. exact : count_size.
  Qed.

  Lemma mkallrel_total R s (x y:T) :
    subseq [:: x; y] (mkallrel R s) -> R x y.
  Proof.
    move : s. apply : (@my_mkallrel_ind _ R) =>[|h s IH]//=.
    rewrite mkallrel_equation /=. case : ifP =>[/eqP->|]//.
    rewrite sub1seq.
      by move /allP : (all_mkallrel R (filter_all (R h) s)) => H /H.
  Qed.

  Definition myundup := @mkallrel T xpredC1.

  Lemma myundup_undup (s:seq T) : myundup s = rev (undup (rev s)).
  Proof.
    rewrite /myundup. move : s.
    apply : (@my_mkallrel_ind _ xpredC1) =>[|x s IH]//.
    rewrite mkallrel_equation IH rev_cons undup_rcons rev_rcons.
      by rewrite -filter_rev filter_undup.
  Qed.

  Lemma myundup_uniq (s:seq T) : uniq (myundup s).
  Proof. by rewrite myundup_undup rev_uniq undup_uniq. Qed.

  Lemma mem_myundup (s:seq T) : myundup s =i s.
  Proof.
    move => x. by rewrite myundup_undup mem_rev mem_undup mem_rev.
  Qed.

  Lemma myundup_subseq (s:seq T) : subseq (myundup s) s.
  Proof.
      by rewrite myundup_undup -[s in subseq _ s]revK subseq_rev undup_subseq.
  Qed.

  Lemma myundup_leq_index x y (s:seq T) :
    index x (myundup s) <= index y (myundup s) = (index x s <= index y s).
  Proof.
    rewrite /myundup. move : s.
    apply : (@my_mkallrel_ind _ xpredC1) =>[|h s IH]//=.
    rewrite mkallrel_equation /=. case : ifP =>// /negbT. rewrite eq_sym => Hx.
    case : ifP =>// /negbT. rewrite eq_sym !ltnS IH => Hy.
    elim : s {IH} =>[|k s IH]//=. symmetry.
    case : ifP =>[/eqP->|]; [by rewrite Hx /= eq_refl|].
    case : ifP =>[/eqP->|]; [by rewrite Hy /= eq_refl =>->|].
      by case : ifP =>/=[_->->|_]; rewrite ltnS -IH.
  Qed.

  Lemma myundup_uniqueness (s0 s:seq T) :
    uniq s ->
    s =i s0 ->
    (forall x y, index x s <= index y s = (index x s0 <= index y s0)) ->
    s = myundup s0.
  Proof.
    rewrite /myundup. move : s0 s.
    apply : (@my_mkallrel_ind _ xpredC1) =>[|x s IH][|x0 s0]//=.
    - move =>_/(_ x0). by rewrite inE eq_refl.
    - move =>_/(_ x). by rewrite inE eq_refl.
    - rewrite mkallrel_equation =>/andP[Hx Hs].
      case : (x =P x0) Hx
      =>[<- Hx|/eqP /negbTE Hx0 Hs0] Hmem H;
          [|move : (H x x0); by rewrite !eq_refl Hx0 eq_sym Hx0].
      congr(_ :: _). apply /IH =>[|y|a b]//.
      + move : (Hmem y). rewrite !inE mem_filter.
          by case : (y =P x) =>[->|]; [move /negbTE : Hx =>->|].
      + move : (H a b). case : ifP =>[/eqP<-_|].
        * move : (Hmem b). rewrite !inE (memNindex Hx) leqNgt index_mem.
          case : (b =P x) =>/=[->|/eqP Hbx ->]; [by rewrite Hx leqnn|].
          rewrite memNindex ?mem_filter ?eq_refl // leqNgt index_mem.
            by rewrite mem_filter Hbx.
        * case : ifP =>[/eqP<-_ _|Ha Hb].
          -- by rewrite ![index x _]memNindex ?mem_filter ?eq_refl //
                        !index_size.
          -- rewrite !ltnS =>->. symmetry. elim : s {IH Hmem H}=>[|y s IH]//=.
             case : (y =P x) =>/=[->|]; [by rewrite IH Ha Hb|].
               by case : ifP =>//=; case : ifP.       
  Qed.
End EqSeq.
