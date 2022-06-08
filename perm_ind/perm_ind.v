From mathcomp
     Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ***************************** *)
Section Perm_ind.
  Variable (T:eqType).

  Lemma perm_ind (P:seq T -> seq T -> Prop) :
    P [::] [::] ->
    (forall u s t, P s u -> P u t -> P s t) ->
    (forall a s t, P s t -> P (a :: s) (a :: t)) ->
    (forall a b s, P [:: a, b & s] [:: b, a & s]) ->
    forall s t, perm_eq s t -> P s t.
  Proof.
    move => Hnil Htrans Hcons Hcons2 s.
    elim : (size s) {-2}s (leqnn (size s))
    =>[|n IHn][|a s']//=; try by move =>_ t; rewrite perm_sym =>/perm_nilP->.
    rewrite ltnS => Hs' [/permP /(_ predT)|b t]// Hperm.
    move : (perm_mem Hperm b) (Hperm).
    rewrite !in_cons eq_refl =>/=/orP[/eqP->|Hb _].
    - rewrite perm_cons =>/(IHn _ Hs'). exact : Hcons.
    - apply : Htrans (Htrans _ _ _ (Hcons a _ _ (IHn _ Hs' _ (perm_to_rem Hb)))
                            (Hcons2 _ _ _)) (Hcons _ _ _ (IHn _ _ _ _)).
      + rewrite /= size_rem //. by case : s' Hs' Hb {Hperm}.
      + rewrite -(perm_cons b). apply : perm_trans Hperm.
          by rewrite -perm_rcons /= perm_cons perm_rcons perm_sym perm_to_rem.
  Qed.

  Lemma perm_eqind (S:Type) (f:seq T -> S) :
    (forall a s t, f s = f t -> f (a :: s) = f (a :: t)) ->
    (forall a b s, f [:: a, b & s] = f [:: b, a & s]) ->
    forall s t, perm_eq s t -> f s = f t.
  Proof.
    move => Hcons Hcons2. by apply : perm_ind =>[|u s t->||].
  Qed.

  Lemma perm_Wr (P:seq T -> seq T -> Prop):
    (forall s t, perm_eq s t -> forall u, P u s -> P u t) ->
    forall s t, perm_eq s t -> P s t -> forall u, perm_eq s u -> P s u.
  Proof.
    move => HPl s t Hpst HPst u Hpsu. apply : HPl HPst.
    apply : perm_trans Hpsu. by rewrite perm_sym.
  Qed.

  Lemma perm_Wl (P:seq T -> seq T -> Prop):
    (forall s t, perm_eq s t -> forall u, P s u -> P t u) ->
    forall s t, perm_eq s t -> P s t -> forall u, perm_eq u t -> P u t.
  Proof.
    move => HPr s t Hpst HPst u Hput. apply : HPr HPst.
    apply : (perm_trans Hpst). by rewrite perm_sym.
  Qed.

  Lemma perm_imply_ind (P Q:seq T -> seq T -> Prop) :
    (forall s t, perm_eq s t -> forall u, P s u -> P t u) ->
    (forall s t, perm_eq s t -> forall u, P u s -> P u t) ->
    (forall a s t, P (a :: s) (a :: t) -> P s t) ->
    Q [::] [::] ->
    (forall u s t, Q s u -> Q u t -> Q s t) ->
    (forall a s t, P (a :: s) (a :: t) -> Q s t -> Q (a :: s) (a :: t)) ->
    (forall a b s,
        P [:: a, b & s] [:: b, a & s] -> Q [:: a, b & s] [:: b, a & s]) ->
    forall s t, perm_eq s t -> P s t -> Q s t.
  Proof.
    move => HPl HPr HPcons Hnil Htrans Hcons Hcons2 s.
    have [n] := ubnP (size s).
    elim : n s =>[|n IHn][|a s]//=;
                         [by move =>_ t; rewrite perm_sym =>/perm_nilP->|].
    rewrite ltnS => Hs [/permP/(_ predT)|b t]// Hperm.
    move : (perm_mem Hperm b) (Hperm).
    rewrite !in_cons eq_refl =>/=/orP[/eqP->|Hb _ HPas].
    - rewrite perm_cons => Hpst HPst.
      exact : Hcons HPst (IHn _ Hs _ Hpst (HPcons _ _ _ HPst)).
    - move : (perm_Wl HPl Hperm HPas) (perm_Wr HPr Hperm HPas) (perm_to_rem Hb)
      => HpPl HpPr Hsb.
      have Hbas : perm_eq [:: b, a & rem b s] (b :: t)
        by apply : perm_trans Hperm;
        rewrite -perm_rcons /= perm_cons perm_rcons perm_sym.
      move : (Hsb). rewrite -(perm_cons a) => Hpasr.
      move : (HpPr _ Hpasr) => HPasr.
      apply : (Htrans _ _ _
                (Hcons _ _ _ HPasr (IHn _ Hs _ Hsb (HPcons _ _ _ HPasr)))).
      apply : Htrans (Hcons2 _ _ _ _) _; [|apply : Hcons; [|apply /IHn]].
      + apply : HPl Hpasr _ (HpPr _ _).
          by rewrite perm_sym -perm_rcons /= perm_cons perm_rcons perm_sym.
      + exact : HpPl.
      + rewrite /= (size_rem Hb).
          by case : s Hb Hs {Hperm HPas HpPr Hsb Hbas Hpasr HPasr}.
      + by rewrite -(perm_cons b).
      + exact : HPcons (HpPl _ _).
  Qed.

 Lemma perm_imply1l_ind (P:seq T -> Prop) (Q:seq T -> seq T -> Prop) :
    (forall s t, perm_eq s t -> P s -> P t) ->
    (forall a s, P (a :: s) -> P s) ->
    Q [::] [::] ->
    (forall u s t, Q s u -> Q u t -> Q s t) ->
    (forall a s t, P (a :: s) -> Q s t -> Q (a :: s) (a :: t)) ->
    (forall a b s, P [:: a, b & s] -> Q [:: a, b & s] [:: b, a & s]) ->
    forall s t, perm_eq s t -> P s -> Q s t.
  Proof.
    move => HP HPcons Hnil Htrans Hcons Hcons2.
    apply : (@perm_imply_ind (fun s t => P s)) =>[s t Hst _||a s _||||]//.
    - exact : HP.
    - exact : HPcons.
  Qed.

  Lemma perm_imply1r_ind (P:seq T -> Prop) (Q:seq T -> seq T -> Prop) :
    (forall s t, perm_eq s t -> P s -> P t) ->
    (forall a s, P (a :: s) -> P s) ->
    Q [::] [::] ->
    (forall u s t, Q s u -> Q u t -> Q s t) ->
    (forall a s t, P (a :: t) -> Q s t -> Q (a :: s) (a :: t)) ->
    (forall a b s, P [:: b, a & s] -> Q [:: a, b & s] [:: b, a & s]) ->
    forall s t, perm_eq s t -> P t -> Q s t.
  Proof.
    move => HP HPcons Hnil Htrans Hcons Hcons2.
    apply : (@perm_imply_ind (fun s t => P t)) =>[|s t Hst _|a _||||]//.
    - exact : HP.
    - exact : HPcons.
  Qed.

(* example *)
  Fixpoint spick (P:pred T) (s:seq T) : option T :=
    if s is x :: s' then if P x then Some x else spick P s' else None.

  Lemma perm_map_spick (S:eqType) (f:T -> S) (s1 s2:seq T):
    perm_eq s1 s2 -> uniq [seq f x | x <- s1] ->
    forall y, spick (eq_op^~ y \o f) s1 = spick (eq_op^~ y \o f) s2.
  Proof.
    move : s1 s2.
    apply : perm_imply1l_ind
    =>[s t /(perm_map f)/perm_uniq->|a s /andP[]|
       |u s t Hsu Hut y|a s t _ H y|a b s]//=.
    - by rewrite Hsu Hut.
    - by rewrite H.
    - rewrite inE negb_or eq_sym =>/and3P[/andP[Hba _] _ _] y.
      case : ifP Hba =>[/eqP->|]//. by case : ifP.
  Qed.
(*
  Variable (P Q:seq T -> seq T -> Prop).

  Goal forall s t, perm_eq s t -> P s t -> Q s t.
  Proof.
    apply : perm_ind.
(*  apply : (@perm_ind (fun s t => P s t -> Q s t)).*)
*)
End Perm_ind.
