From mathcomp
     Require Import all_ssreflect.
Require Import Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ***************************** *)
Section SSeq.
(*
  Inductive sseq : Type -> Type :=
  | snil T: sseq T
  | scons T: T -> sseq (sseq T) -> sseq T.
*)
  Notation empty := Empty_set.

  Inductive bitree (T:Type) : Type :=
  | BiLeaf : bitree T
  | BiNode of T & bitree T & bitree T.

  Fixpoint bitree_eq (T:eqType) (t t':bitree T) : bool :=
    match t, t' with
    | BiLeaf,BiLeaf => true
    | BiLeaf,BiNode _ _ _ => false
    | BiNode _ _ _,BiLeaf => false
    | BiNode x tl tr,BiNode x' tl' tr' =>
      [&& x == x', bitree_eq tl tl' & bitree_eq tr tr']
    end.

  Lemma bitree_eqP (T:eqType) : Equality.axiom (@bitree_eq T).
  Proof.
    move => t t'. apply /(iffP idP) =>[|<-].
    - by elim : t t'
      =>[|x tl IHl tr IHr][|x' tl' tr']//=/and3P[/eqP<-/IHl<-/IHr<-].
    - elim : t =>[|x tl IHl tr IHr]//=. by rewrite eq_refl IHl IHr.
  Qed.

  Fixpoint minheight (T:Type) (t:bitree T) : nat :=
    if t is BiNode _ tl tr then (minn (minheight tl) (minheight tr)).+1 else 0.

  Fixpoint maxheight (T:Type) (t:bitree T) : nat :=
    if t is BiNode _ tl tr then (maxn (maxheight tl) (maxheight tr)).+1 else 0.

  Fixpoint leftheight (T:Type) (t:bitree T) : nat :=
    if t is BiNode _ tl _ then (leftheight tl).+1 else 0.

  Lemma bitree_ltn_ind (T:Type) (P:bitree T -> Prop) :
    (forall t, (forall s, maxheight s < maxheight t -> P s) -> P t) ->
    forall t, P t.
  Proof.
    move => H t. have [n] := ubnP (maxheight t).
      by elim : n t =>[|n IH][|a tl tr]//= Ht;
                        apply /H => t // /leq_trans/(_ Ht)/IH.
  Qed.
(*
Inductive seq : Type -> Type :=
| Nil A : seq A
| Cons A : A -> seq A -> seq A.
*)

(*
  Inductive sseq : Type -> Type :=
  | SseqNil A : sseq A
  | SseqCons A : A -> sseq (sseq A) -> sseq A.
 *)
  (* Error: Universe inconsistency *)

  Fixpoint sseq_rec (A:Type) (d:nat) (t:bitree unit) : Type :=
    if d is d'.+1
    then if t is BiNode _ tl tr
         then sseq_rec A d' tl * sseq_rec A d'.+2 tr else unit
    else if t is BiNode _ _ _ then empty else A.

  Fixpoint eqsseq_rec (A:eqType) (d:nat) (t:bitree unit) :
    rel (sseq_rec A d t) :=
    match d,t return rel (sseq_rec A d t) with
    | 0, BiLeaf => fun x y => x == y
    | 0, BiNode _ _ _ => fun _ _ => true
    | _.+1, BiLeaf => fun _ _ => true
    | d'.+1, BiNode _ tl tr =>
      fun x y => eqsseq_rec x.1 y.1 && eqsseq_rec x.2 y.2
    end.

  Lemma eqsseq_recP (A:eqType) (d:nat) (t:bitree unit) :
    Equality.axiom (@eqsseq_rec A d t).
  Proof.
    elim : t d =>[|[] tl IHl tr IHr][|d]//=; [move => s r; exact /eqP| |].
    - case =>[][]. by constructor.
    - case =>[x1 x2][y1 y2]/=.
      apply /(iffP idP) =>[/andP[/IHl/=->/IHr/=->]|[->->]]//.
      apply /andP. split; [exact /IHl|exact /IHr].
  Qed.

  Fixpoint exbase (T:Type) (d:nat) (t:bitree T) : bool :=
    if t is BiNode _ tl tr
    then if d is d'.+1 then exbase d' tl || exbase d'.+2 tr else false
    else d == 0.

  Definition sseq_rec_map_not_exheight  (A B:Type) (d:nat) (t:bitree unit):
    exbase d t = false -> sseq_rec A d t -> sseq_rec B d t.
  Proof.
    elim : t d =>[|_ tl IHl tr IHr][|d]//=.
    case : (exbase d tl) (IHl d) =>// /(_ (erefl _)) fl /IHr fr [/fl l /fr r].
    exact : pair.
  Defined.

  Definition sseq_rec_map_ltn (A B:Type) (d:nat) (t:bitree unit) :
    maxheight t < d -> sseq_rec A d t -> sseq_rec B d t.
  Proof.
    elim : t d =>[|_ tl IHl tr IHr][|d]//=. rewrite ltnS gtn_max.
    case : (maxheight tl < d) (IHl d) =>// /(_ (erefl _)) Hl.
    move =>/((@leq_trans _ _ _)^~ (leqW (leqnSn d)))/IHr Hr [/Hl l /Hr r].
    exact : pair.
  Defined.

  Definition sseq_rec_empty (A:Type) (d:nat) (t:bitree unit) :
    d < leftheight t -> sseq_rec A d t -> empty.
  Proof.
      by elim : t d =>[|_ tl IHl tr _][|d]//= Hd [/(IHl _ Hd)].
  Defined.

  Fixpoint liftedtree (d:nat) (t0 t:bitree unit) : bitree unit :=
    if t is BiNode x tl tr
    then if d is d'.+1
         then BiNode x (liftedtree d' t0 tl) (liftedtree d'.+2 t0 tr)
         else t
    else if d is d'.+1 then t else t0.

  Definition sseq_rec_lift (A:Type) (d k:nat) (t0 t:bitree unit) :
    sseq_rec (sseq_rec A d t0) k t -> sseq_rec A (k + d) (liftedtree k t0 t).
  Proof.
    elim : t k =>[|[] tl IHl tr IHr][|k]//=[/IHl l /IHr] r. exact : pair.
  Defined.


  Definition sseqn (A:Type) (d:nat) := sigT (sseq_rec A d).


  Definition from_sseq0 (A:Type) (x:sseqn A 0) : A :=
    match x with
    | existT t s => let f : sseq_rec A 0 t -> A :=
                        match t return sseq_rec A 0 t -> A with
                        | BiLeaf => id
                        | BiNode _ _ _ => fun x => match x with end
                        end
                    in f s
    end.

  Definition to_sseq0 (A:Type) : A -> sseqn A 0 := existT _ (BiLeaf _).

  Lemma to_from_sseq0 (A:Type) : cancel (@from_sseq0 A) (@to_sseq0 _).
  Proof. by case =>[[|? ? ? []]]. Qed.

  Lemma from_to_sseq0 (A:Type) : cancel (@to_sseq0 A) (@from_sseq0 _).
  Proof. done. Qed.


  Fixpoint sseqn_lift_rec (A:Type) (d:nat) (t:bitree unit) :
    forall k:nat, sseq_rec (sseqn A d) k t -> sseqn A (k + d) :=
    match t return forall k, sseq_rec (sseqn A d) k t -> sseqn A (k + d) with
    | BiLeaf =>
      fun k =>
        match k return sseq_rec (sseqn A d) k (BiLeaf _) -> sseqn A (k + d) with
        | 0 => id
        | k'.+1 => fun u => existT _ (BiLeaf _) tt
        end
    | BiNode u tl tr =>
      fun k =>
        match k
              return sseq_rec (sseqn A d) k (BiNode u tl tr) ->
                     sseqn A (k + d) with
        | 0 => fun e => match e with end
        | k'.+1 =>
          fun x => match x with
                   | pair sl sr =>
                     match (sseqn_lift_rec sl),(sseqn_lift_rec sr) with
                     | existT tl' xl, existT tr' xr =>
                       existT _ (BiNode u _ _) (pair xl xr)
                     end
                   end
        end
    end.

  Definition sseqn_lift (A:Type) (k d:nat) :
    sseqn (sseqn A d) k -> sseqn A (k + d) :=
    fun x => match x with
             | existT _ x => sseqn_lift_rec x
             end.


  Fixpoint sseqn_unlift_rec (A:Type) (d:nat) (t:bitree unit):
    forall k:nat, sseq_rec A (k + d) t -> sseqn (sseqn A d) k :=
    match t return forall k, sseq_rec A (k + d) t -> sseqn (sseqn A d) k with
    | BiLeaf =>
      fun k =>
        match k return sseq_rec A (k + d) (BiLeaf _) -> sseqn (sseqn A d) k with
        | 0 => existT _ (BiLeaf _) \o existT _ (BiLeaf _)
        | k'.+1 => fun u => existT _ (BiLeaf _) tt
        end
    | BiNode u tl tr =>
      fun k =>
        match k return sseq_rec A (k + d) (BiNode u tl tr) ->
                       sseqn (sseqn A d) k with
        | 0 => existT _ (BiLeaf _) \o existT _ (BiNode u tl tr)
        | k'.+1 =>
          fun x => match x with
                   | pair sl sr =>
                     match (sseqn_unlift_rec sl),
                           (@sseqn_unlift_rec _ _ _ k'.+2 sr) with
                     | existT tl' xl, existT tr' xr =>
                       existT _ (BiNode u _ _) (pair xl xr)
                     end
                   end
        end
    end.

  Definition sseqn_unlift (A:Type) (k d:nat):
    sseqn A (k + d) -> sseqn (sseqn A d) k :=
    fun x => match x with
             | existT _ x => sseqn_unlift_rec x
             end.

  Lemma sseqn_lift_unlift (A:Type) (k d:nat):
    cancel (@sseqn_unlift A k d) (@sseqn_lift _ _ _).
  Proof.
    case => t. elim : t k =>[|[] tl IHl tr IHr][|k]//=[]//= l r.
    case : (IHl k l) (IHr k.+2 r) =>/=.
    by case : (sseqn_unlift_rec l)  (@sseqn_unlift_rec _ _ _ k.+2 r)
    =>[tl' xl'][tr' xr']/=->->.
  Qed.

  Lemma sseqn_unlift_lift (A:Type) (k d:nat):
    cancel (@sseqn_lift A k d) (@sseqn_unlift _ _ _).
  Proof.
    case => t. elim : t k =>[|[] tl IHl tr IHr][|k]//=[]//.
    - move => t. by elim : t d =>[|[] tl IHl tr IHr][|d].
    - move => l r. move : (IHl k l) (IHr k.+2 r) =>/=.
      by case : (sseqn_lift_rec l) (@sseqn_lift_rec _ _ _ k.+2 r)
      =>[tl' xl'][tr' xr']/=->->.
  Qed.
(*
  Definition cast_sseq_rec (A:Type) (d e:nat) (t:bitree unit) (H:d = e)
             (x:sseq_rec A d t) : sseq_rec A e t
    := eq_rect _ ((sseq_rec A)^~ t) x _ H.
 *)

  Definition from_eq (A:eqType) (x y:A) : x == y -> x = y :=
    elimTF (@eqP _ _ _).

  Definition to_eq (A:eqType) (x y:A) : x = y -> x == y :=
    @introTF _ _ true (@eqP _ _ _).

  Definition eq_trans (A:eqType) (y x z:A) (Hxy:x == y) (Hyz:y == z) : x == z
    := to_eq (etrans (from_eq Hxy) (from_eq Hyz)).

  Definition mkeq_sym (A:eqType) (x y:A) (H:x == y) : y == x :=
    to_eq (esym (from_eq H)).

  Lemma to_from_eq (A:eqType) (x y:A): cancel (@from_eq _ x y) (@to_eq _ _ _).
  Proof. move => H. exact : eq_irrelevance. Qed.

  Lemma from_to_eq (A:eqType) (x y:A):
    cancel (@to_eq _ x y) (@from_eq _ _ _).
  Proof. move => H. exact : eq_irrelevance. Qed.

(*
  Definition eq_to_prop (A:eqType) (x y:A) : x == y -> x = y :=
    match (@eqP _ x y) return x == y -> x = y with
    | ReflectT H => fun => H
    | ReflectF H => fun i => False_ind _ i
    end.
  Proof.
    by case : (@eqP _ x y). Defined.
*)
(*
  Definition cast_sseq_rec (A:Type) (d e:nat) (t:bitree unit) (H:d == e)
             (x:sseq_rec A d t) : sseq_rec A e t
    := eq_rect _ ((sseq_rec A)^~ t) x _ (from_eq H).

  Definition cast_sseq_rec_id (A:Type) (d:nat) (t:bitree unit) (H:d == d)
             (x:sseq_rec A d t) : cast_sseq_rec H x = x.
  Proof.
    rewrite /cast_sseq_rec -Eqdep_dec.eq_rect_eq_dec =>// n m.
      by case : (@eqP _ n m); [left|right].
  Qed.

  Lemma cast_sseq_rec_comp (A:Type) (d e f:nat) (t:bitree unit)
        (Hde:d == e) (Hef:e == f) (x:sseq_rec A d t):
    cast_sseq_rec Hef (cast_sseq_rec Hde x) =
    cast_sseq_rec (eq_trans Hde Hef) x.
  Proof.
    rewrite /eq_trans/cast_sseq_rec from_to_eq.
    exact /esym/(@eq_trans_map _ ((sseq_rec A)^~ t))/erefl/erefl.
  Qed.

  Lemma cast_sseq_rec_ordK (A:Type) (d e:nat) (t:bitree unit) (H:d == e):
    cancel (@cast_sseq_rec A _ _ t H) (@cast_sseq_rec _ _ _ _ (mkeq_sym H)).
  Proof.
    move => x. rewrite cast_sseq_rec_comp. exact /cast_sseq_rec_id.
  Qed.

  Lemma cast_sseq_rec_ordKV (A:Type) (d e:nat) (t:bitree unit) (H:d == e):
    cancel (@cast_sseq_rec A _ _ t (mkeq_sym H)) (@cast_sseq_rec _ _ _ _ H).
  Proof.
    move => x. rewrite cast_sseq_rec_comp. exact /cast_sseq_rec_id.
  Qed.

  Definition cast_sseqn (A:Type) (d e:nat) (H:d == e) (x:sseqn A d) :
    sseqn A e := match x with
                 | existT _ y => existT _ _ (cast_sseq_rec H y)
                 end.

  Lemma cast_sseqn_id (A:Type) (d:nat) (H:d == d) (x:sseqn A d):
    cast_sseqn H x = x.
  Proof. case : x => t x /=. by rewrite cast_sseq_rec_id. Qed.

  Lemma cast_sseqn_comp (A:Type) (d e f:nat) (Hde:d == e) (Hef:e == f)
        (x:sseqn A d):
    cast_sseqn Hef (cast_sseqn Hde x) = cast_sseqn (eq_trans Hde Hef) x.
  Proof. case : x => t x /=. by rewrite cast_sseq_rec_comp. Qed.

  Lemma cast_sseqn_ordK (A:Type) (d e:nat) (H:d == e):
    cancel (@cast_sseqn A _ _ H) (@cast_sseqn _ _ _ (mkeq_sym H)).
  Proof. case => t x /=. by rewrite cast_sseq_rec_ordK. Qed.
    
  Lemma cast_sseqn_ordKV (A:Type) (d e:nat) (H:d == e):
    cancel (@cast_sseqn A _ _ (mkeq_sym H)) (@cast_sseqn _ _ _ H).
  Proof. case => t x /=. by rewrite cast_sseq_rec_ordKV. Qed.
 *)
  Definition cast_sseq_rec (A:Type) (d e:nat) (t:bitree unit) (H:d = e)
             (x:sseq_rec A d t) : sseq_rec A e t
    := eq_rect _ ((sseq_rec A)^~ t) x _ H.

  Definition cast_sseq_rec_id (A:Type) (d:nat) (t:bitree unit) (H:d = d)
             (x:sseq_rec A d t) : cast_sseq_rec H x = x.
  Proof.
    rewrite /cast_sseq_rec -Eqdep_dec.eq_rect_eq_dec =>// n m.
      by case : (@eqP _ n m); [left|right].
  Qed.

  Lemma cast_sseq_rec_comp (A:Type) (d e f:nat) (t:bitree unit)
        (Hde:d = e) (Hef:e = f) (x:sseq_rec A d t):
    cast_sseq_rec Hef (cast_sseq_rec Hde x) =
    cast_sseq_rec (etrans Hde Hef) x.
  Proof.
    exact /(@rew_compose _ ((sseq_rec A)^~ t)).
  Qed.

  Lemma cast_sseq_rec_ordK (A:Type) (d e:nat) (t:bitree unit) (H:d = e):
    cancel (@cast_sseq_rec A _ _ t H) (@cast_sseq_rec _ _ _ _ (esym H)).
  Proof.
    move => x. rewrite cast_sseq_rec_comp. exact /cast_sseq_rec_id.
  Qed.

  Lemma cast_sseq_rec_ordKV (A:Type) (d e:nat) (t:bitree unit) (H:d = e):
    cancel (@cast_sseq_rec A _ _ t (esym H)) (@cast_sseq_rec _ _ _ _ H).
  Proof.
    move => x. rewrite cast_sseq_rec_comp. exact /cast_sseq_rec_id.
  Qed.

  Definition cast_sseqn (A:Type) (d e:nat) (H:d = e) (x:sseqn A d) :
    sseqn A e := match x with
                 | existT _ y => existT _ _ (cast_sseq_rec H y)
                 end.

  Lemma cast_sseqn_id (A:Type) (d:nat) (H:d = d) (x:sseqn A d):
    cast_sseqn H x = x.
  Proof. case : x => t x /=. by rewrite cast_sseq_rec_id. Qed.

  Lemma cast_sseqn_comp (A:Type) (d e f:nat) (Hde:d = e) (Hef:e = f)
        (x:sseqn A d):
    cast_sseqn Hef (cast_sseqn Hde x) = cast_sseqn (etrans Hde Hef) x.
  Proof. case : x => t x /=. by rewrite cast_sseq_rec_comp. Qed.

  Lemma cast_sseqn_ordK (A:Type) (d e:nat) (H:d = e):
    cancel (@cast_sseqn A _ _ H) (@cast_sseqn _ _ _ (esym H)).
  Proof. case => t x /=. by rewrite cast_sseq_rec_ordK. Qed.
    
  Lemma cast_sseqn_ordKV (A:Type) (d e:nat) (H:d = e):
    cancel (@cast_sseqn A _ _ (esym H)) (@cast_sseqn _ _ _ H).
  Proof. case => t x /=. by rewrite cast_sseq_rec_ordKV. Qed.

(*
  Lemma sseqn_unlift_rec_BiNodeS' (A:Type) (k d:nat) (u:unit)
        (tl tr:bitree unit) (xl:sseq_rec A (k + d) tl)
        (xr:sseq_rec A (k + d).+2 tr) (tl' tr':bitree unit) xl' xr':
          sseqn_unlift_rec xl = existT _ tl' xl' ->
          @sseqn_unlift_rec _ _ _ k.+2 xr = existT _ tr' xr' ->
          @sseqn_unlift_rec _ d (BiNode u tl tr) k.+1 (pair xl xr) =
          existT _ (BiNode u tl' tr') (pair xl' xr').
  Proof. by move =>/=->->. Qed.
Print sseqn_unlift_rec_BiNodeS'.   
    
 Definition sseqn_unlift_rec_BiNodeS (A:Type) (k d:nat) (u:unit)
        (tl tr:bitree unit) (xl:sseq_rec A (k + d) tl)
        (xr:sseq_rec A (k + d).+2 tr) :=
   @sseqn_unlift_rec_BiNodeS' A k d u tl tr xl xr
                              (let: existT t _ := sseqn_unlift_rec xl in t)
                              (let: existT t _ := @sseqn_unlift_rec _ _ _ k.+2 xr in t)
                              (let: existT _ x := sseqn_unlift_rec xl in x)
                              (let: existT _ x := sseqn_unlift_rec xr in x).
   tl' tr' xl' xr':
          sseqn_unlift_rec xl = existT _ tl' xl' ->
          @sseqn_unlift_rec _ _ _ k.+2 xr = existT _ tr' xr' ->
          @sseqn_unlift_rec _ d (BiNode u tl tr) k.+1 (pair xl xr) =
          existT _ (BiNode u
                           (let: existT tl'' _ := sseqn_unlift_rec xl in tl'') tr') (pair xl' xr').
*)
(*
  Definition sseqn_lift' (A:Type) (k d:nat):
    sseqn (sseqn A d) k -> sseqn A (k + d).
  Proof.
    case =>[t]. elim : t k =>[|[] tl IHl tr IHr][|k]//=.
    - move =>_. exact /(existT _ (BiLeaf _) tt).
    - case =>/IHl[tl' xl]/IHr[tr' xr].
      exact /(existT _ (BiNode tt _ _) (pair xl xr)).
  Defined.

  Definition sseqn_unlift' (A:Type) (k d:nat):
    sseqn A (k + d) -> sseqn (sseqn A d) k.
  Proof.
    case =>[t]. elim : t k =>[|[] tl IHl tr IHr][|k].
    - move => x. exact /(existT _ (BiLeaf _))/(existT _ (BiLeaf _)).
    - move => u. exact /(existT _ (BiLeaf _)).
    - move => x. exact /(existT _ (BiLeaf _))/(existT _ (BiNode tt tl tr)).
    - move =>[/IHl[tl' xl]/(@IHr k.+2)[tr' xr]].
      exact /(existT _ (BiNode tt tl' tr'))/pair.
  Defined.
 *)

  Fixpoint sseq_rec_map (A B:Type) (d:nat) (t:bitree unit) (f:A -> B):
    sseq_rec A d t -> sseq_rec B d t :=
    match d,t return sseq_rec A d t -> sseq_rec B d t with
    | 0,BiLeaf => f
    | 0,BiNode _ _ _ => id
    | _.+1,BiLeaf => id
    | _.+1,BiNode _ _ _ => fun x => (sseq_rec_map f x.1,sseq_rec_map f x.2)
    end.

  Lemma sseq_rec_map_id (A:Type) (d:nat) (t:bitree unit) (x:sseq_rec A d t):
    sseq_rec_map id x = x.
  Proof.
    elim : t d x =>[|[] tl IHl tr IHr][|d]//=[l r]. by rewrite IHl IHr.
  Qed.

  Lemma sseq_rec_map_comp (A B C:Type) (d:nat) (t:bitree unit)
        (f:A -> B) (g:B -> C) (x:sseq_rec A d t):
    sseq_rec_map (g \o f) x = sseq_rec_map g (sseq_rec_map f x).
  Proof.
    elim : t d x =>[|[] tl IHl tr IHr][|d]//=[l r]. by rewrite IHl IHr.
  Qed.

  Lemma eq_sseq_rec_map (A B:Type) (d:nat) (t:bitree unit) (f g:A -> B):
    f =1 g -> @sseq_rec_map _ _ d t f =1 sseq_rec_map g.
  Proof.
    move => H. elim : t d =>[|[] tl IHl tr IHr][|d]//=[l r]. by rewrite IHl IHr.
  Qed.

  Definition sseqn_map (A B:Type) (d:nat) (f:A -> B) (x:sseqn A d) :
    sseqn B d :=
    match x with
    | existT t p => existT _ t (sseq_rec_map f p)
    end.

  Lemma sseqn_map_id (A:Type) (d:nat) (x:sseqn A d): sseqn_map id x = x.
  Proof. case : x => t x. by rewrite /sseqn_map sseq_rec_map_id. Qed.

  Lemma sseqn_map_comp (A B C:Type) (d:nat) (f:A -> B) (g:B -> C) (x:sseqn A d):
    sseqn_map (g \o f) x = sseqn_map g (sseqn_map f x).
  Proof. case : x => t x. by rewrite /sseqn_map sseq_rec_map_comp. Qed.

  Lemma eq_sseqn_map (A B:Type) (d:nat) (f g:A -> B) :
    f =1 g -> @sseqn_map _ _ d f =1 sseqn_map g.
  Proof.
    move => H. case =>[t x]. by rewrite /sseqn_map (eq_sseq_rec_map H).
  Qed.


  Fixpoint sseq_lift_recd0 (A:Type) (t:bitree unit):
    forall d:nat, sseq_rec A (d + 0) t -> sseq_rec A d t :=
    match t return forall d, sseq_rec A (d + 0) t -> sseq_rec A d t with
    | BiLeaf =>
      fun d => match d return sseq_rec A (d + 0) (BiLeaf _) ->
                              sseq_rec A d (BiLeaf _) with
               | 0 => id
               | _ => id
               end
    | BiNode u tl tr =>
      fun d => match d return sseq_rec A (d + 0) (BiNode _ _ _) ->
                              sseq_rec A d (BiNode _ _ _) with
               | 0 => id
               | d'.+1 => fun x =>
                            pair (sseq_lift_recd0 x.1)
                                 (@sseq_lift_recd0 _ _ d'.+2 x.2)
               end
    end.

  Definition sseqn_liftd0 (A:Type) (d:nat) (x:sseqn A (d + 0)) : sseqn A d :=
    match x with
    | existT _ x => existT _ _ (sseq_lift_recd0 x)
    end.

  Fixpoint sseq_unlift_recd0 (A:Type) (t:bitree unit):
    forall d:nat, sseq_rec A d t -> sseq_rec A (d + 0) t :=
    match t return forall d, sseq_rec A d t -> sseq_rec A (d + 0) t with
    | BiLeaf =>
      fun d => match d return sseq_rec A d (BiLeaf _) ->
                              sseq_rec A (d + 0) (BiLeaf _) with
               | 0 => id
               | _ => id
               end
    | BiNode u tl tr =>
      fun d => match d return sseq_rec A d (BiNode _ _ _) ->
                              sseq_rec A (d + 0) (BiNode _ _ _) with
               | 0 => id
               | d'.+1 => fun x =>
                            pair (sseq_unlift_recd0 x.1)
                                 (@sseq_unlift_recd0 _ _ d'.+2 x.2)
               end
    end.

  Definition sseqn_unliftd0 (A:Type) (d:nat) (x:sseqn A d) : sseqn A (d + 0) :=
    match x with
    | existT _ x => existT _ _ (sseq_unlift_recd0 x)
    end.

  Lemma sseq_unlift_lift_recd0 (A:Type) (d:nat) (t:bitree unit):
    cancel (@sseq_lift_recd0 A t d) (@sseq_unlift_recd0 _ _ _).
  Proof.
    move => x. elim : t d x =>[|[] tl IHl tr IHr][|k]//=[xl xr]/=.
      by rewrite IHl IHr.
  Qed.

  Lemma sseq_lift_unlift_recd0 (A:Type) (d:nat) (t:bitree unit):
    cancel (@sseq_unlift_recd0 A t d) (@sseq_lift_recd0 _ _ _).
  Proof.
    move => x. elim : t d x =>[|[] tl IHl tr IHr][|k]//=[xl xr]/=.
      by rewrite IHl IHr.
  Qed.

  Lemma sseqn_unlift_liftd0 (A:Type) (d:nat):
    cancel (@sseqn_liftd0 A d) (@sseqn_unliftd0 _ _).
  Proof.
    case => t p /=. by rewrite sseq_unlift_lift_recd0.
  Qed.

  Lemma sseqn_lift_unliftd0 (A:Type) (d:nat):
    cancel (@sseqn_unliftd0 A d) (@sseqn_liftd0 _ _).
  Proof.
    case => t p /=. by rewrite sseq_lift_unlift_recd0.
  Qed.

  Fixpoint addn0_proof (n:nat) : n + 0 = n :=
    match n return n + 0 = n with
    | 0 => erefl
    | n'.+1 => f_equal S (addn0_proof n')
    end.
(*
  Lemma cast_sseq_rec_liftd0 (A:Type) (d:nat) (t:bitree unit)
        (x:sseq_rec A d t):
    cast_sseq_rec (esym (addn0_proof _)) x = sseq_unlift_recd0 x.
  Proof.
    elim : t d x =>[|[] tl IHl tr IHr][|k]//=.
    - case =>[]. by rewrite unitE.
    - case =>[xl xr]/=.
      rewrite -IHl -IHr /=/cast_sseq_rec/esym !(@eq_sym_map_distr _ _ _ _ S).
*)
(*      Print map_subst_map. Print rew_pair.
      move : (esym (addn0_proof k.+2)) => H2.
      move : (esym (addn0_proof k.+1)) => H1.
      move : (esym (addn0_proof k)) => H.*)
  (**)
  (*
      have : forall (H:k = k + 0) (H1:k.+1 = (k + 0).+1) (H2:k.+2 = (k + 0).+2)
                    (xl:sseq_rec A k tl) (xr:sseq_rec A k.+2 tr),
          eq_rect k.+1 ((sseq_rec A)^~ (BiNode tt tl tr)) (xl, xr)
                  (k.+1 + 0) H1 =
          (eq_rect k ((sseq_rec A)^~ tl) xl (k + 0) H,
           eq_rect k.+2 ((sseq_rec A)^~ tr) xr (k.+2 + 0) H2)
        := fun H H1 H2 =>
             match H,H1,H2 return
                   forall (xl:sseq_rec A k tl) (xr:sseq_rec A k.+2 tr),
                     eq_rect k.+1 ((sseq_rec A)^~ (BiNode tt tl tr)) (xl, xr)
                             (k.+1 + 0) H1 =
                     (eq_rect k ((sseq_rec A)^~ tl) xl (k + 0) H,
                      eq_rect k.+2 ((sseq_rec A)^~ tr) xr (k.+2 + 0) H2) with
             | erefl, erefl, erefl => fun xl xr => erefl _ _
             end.
*)

(*      move : (addn0_proof k).
      have : forall H : k + 0 = k,
          eq_rect k.+1 ((sseq_rec A)^~ (BiNode tt tl tr)) (xl, xr) (k + 0).+1
                  (f_equal S (esym H)) =
          (eq_rect k ((sseq_rec A)^~ tl) xl (k + 0) (esym H),
           eq_rect k.+2 ((sseq_rec A)^~ tr) xr (k + 0).+2
                   (f_equal S (f_equal S (esym H))))
        := fun H : k + 0 = k =>
             match H return
                   eq_rect k.+1 ((sseq_rec A)^~ (BiNode tt tl tr)) (xl, xr)
                           (k + 0).+1 (f_equal S (esym H)) =
                   (eq_rect k ((sseq_rec A)^~ tl) xl (k + 0) (esym H),
                    eq_rect k.+2 ((sseq_rec A)^~ tr) xr (k + 0).+2
                            (f_equal S (f_equal S (esym H))))
             with
             | erefl => erefl _ _
             end. *)

  Lemma sseqn_unlift0 (A:Type) (d:nat) (x:sseqn A d):
    sseqn_unlift (sseqn_unliftd0 x) = sseqn_map (@to_sseq0 _) x.
  Proof.
    case : x => t. elim : t d =>[|[] tl IHl tr IHr][|k]//=[]//= xl xr.
      by move : (IHl _ xl) (IHr _ xr) =>/=->->.
  Qed.
(*
  Lemma sseqn_unlift2 (A:Type) (x:sseqn A 2):
    @sseqn_unlift _ 2 0 x = sseqn_map (@to_sseq0 _) x.
  Proof.
    rewrite -sseqn_unlift0. congr(sseqn_unlift _).

  Proof.
 *)
  (*
  Lemma sseqn_lift_unliftS (A:Type) (k d:nat) (x:sseqn (sseqn A d) k.+1):
    sseqn_lift x =
    sseqn_lift (sseqn_map (@sseqn_lift _ _ _) (@sseqn_unlift _ 1 _ x)).
  Proof.
    case : x => t. elim : t k =>[|[] tl IHl tr IHr]//=[|k][]/=.
    - case : tl {IHl}=>[|[] tll tlr]//=[td xd] xr. move : (IHr _ xr) =>/=->.

      case : (@sseqn_unlift_rec _ _ _ 2 xr).
      case : tr xr {IHr} =>[|[] tl tr]//=[xl xr].
      move =>/=. 
      move : (@sseqn_unlift_rec _ _ _ 1 xr) (IHr _ xr) =>/=[t _]->. move =>/=.
   *)
  (*
  Lemma sseqn_liftS (A:Type) (k d:nat) (x:sseqn (sseqn (sseqn A d) k) 1):
    sseqn_lift (sseqn_lift x) = sseqn_lift (sseqn_map (@sseqn_lift _ _ _) x).
  Proof.
    case : x => t. elim : t k =>[|[] tl IHl tr IHr]//=[|k][]/=.
    - case : tl {IHl}=>[|[] tll tlr]//=[[]]//=[td xd].
      case : tr =>[|[] trl trr]/= in IHr *.
    case : t =>[|[] tl tr]//=.
    case : tl IHl =>[|[] tll tlr].
*)

(*
  Lemma sseqn_unliftS (A:Type) (k d:nat) (x:sseqn A (k + d).+1):
    @sseqn_unlift _ 1 k (@sseqn_unlift _ k.+1 d x) =
    sseqn_map (@sseqn_unlift _ k d) (@sseqn_unlift _ 1 (k + d) x).
  Proof.
    case : x => t. elim /bitree_ltn_ind : t k =>[][|[] tl tr] IH //=[|k][xl xr].
    - case : (sseqn_unlift_rec xl) =>[[]]//= xl'.
      case : tr xr IH =>[|[] trl trr]/=[].
      + by case : xl' =>[[]].
      + move => xrl xrr IH. move : (IH trl). _ 0 xrl).

      case : (@sseqn_unlift_rec _ _ _ 2 xr) =>[]. [[]|[]]]//=.
      +
      +

    elim : t k =>[|[] tl IHl tr IHr]//=[|k]//=[xl xr].
    - case : (sseqn_unlift_rec xl) =>[[]]//= xl'.
      case : (@sseqn_unlift_rec _ _ _ 2 xr) =>/=. (IHr 1 xr) =>/=.
    ; last first.
    - move : (IHl k xl) (IHr k.+2 xr) =>/=.
      case : (sseqn_unlift_rec xl) =>[tl' xl'].
      case : (@sseqn_unlift_rec _ _ _ k.+3 xr) =>[tr' xr']/=.
      case : tl' xl' =>[|[] tll tlr]/=[]//=.
      case : (@sseqn_unlift_rec _ _ _ 2 xr').
    
    - move : (IHr 1 xr) =>/=.      case : (@sseqn_unlift_rec _ _ _ 2 xr) =>[tr' xr']/=. case : (
      case : (sseqn_unlift_rec xl) (IHr 1 xr) =>[[|[] tll tlr]//= xl'].
      move =>/=.

    case : t =>[|[] tl tr]/=.
  Lemma sseqn_unlift2 (A:Type) (d:nat) (x:sseqn A d.+2):
    @sseqn_unlift _ 1 _ (@sseqn_unlift _ 2 _ x) =
    sseqn_map (@sseqn_unlift _ 1 _) (@sseqn_unlift _ 1 _ x).
  Proof.
*)

  Fixpoint iter_sseqn (A:Type) (k d:nat) :
    iter _ d (sseqn^~ k) A -> sseqn A (d * k) :=
    match d return iter _ d (sseqn^~ k) A -> sseqn A (d * k) with
    | 0 => @to_sseq0 _
    | d'.+1 => @sseqn_lift _ _ _ \o sseqn_map (@iter_sseqn _ k d')
    end.

  Fixpoint sseqn_iter (A:Type) (k d:nat) :
    sseqn A (d * k) -> iter _ d (sseqn^~ k) A :=
    match d return sseqn A (d * k) -> iter _ d (sseqn^~ k) A with
    | 0 => @from_sseq0 _
    | d'.+1 => sseqn_map (@sseqn_iter _ k d') \o @sseqn_unlift _ _ _
    end.

  Lemma iter_sseqn_iter (A:Type) (k d:nat):
    cancel (@iter_sseqn A k d) (@sseqn_iter _ _ _).
  Proof.
    elim : d =>[|d IH]//= x /=. rewrite sseqn_unlift_lift -sseqn_map_comp.
    rewrite (@eq_sseqn_map _ _ _ _ id); [exact /sseqn_map_id|exact /IH].
  Qed.

  Lemma sseqn_iter_sseqn (A:Type) (k d:nat):
    cancel (@sseqn_iter A k d) (@iter_sseqn _ _ _).
  Proof.
    elim : d =>[|d IH]//= x /=; [exact /to_from_sseq0|].
    rewrite -sseqn_map_comp (@eq_sseqn_map _ _ _ _ id); [|exact /IH].
      by rewrite sseqn_map_id sseqn_lift_unlift.
  Qed.

  Definition sseqnNil (A:Type) (d:nat) : sseqn A d.+1 := existT _ (BiLeaf _) tt.
  Definition sseqnCons (A:Type) (d:nat) :
    sseqn A d -> sseqn A d.+2 -> sseqn A d.+1 :=
    fun a s =>
      match a, s with
      | existT tl xl, existT tr xr => existT _ (BiNode tt tl tr) (pair xl xr)
      end.


  Definition sseq (A:Type) : Type := sseqn A 1.

  Fixpoint iter_sseq (A:Type) (d:nat) : iter _ d sseq A -> sseqn A d :=
    match d return iter _ d sseq A -> sseqn A d with
    | 0 => @to_sseq0 _
    | d'.+1 => @sseqn_lift _ _ _ \o sseqn_map (@iter_sseq _ d')
    end.

  Fixpoint sseq_iter (A:Type) (d:nat) : sseqn A d -> iter _ d sseq A :=
    match d return sseqn A d -> iter _ d sseq A with
    | 0 => @from_sseq0 _
    | d'.+1 => sseqn_map (@sseq_iter _ d') \o @sseqn_unlift _ 1 _
    end.

  Lemma iter_sseq_iter (A:Type) (d:nat):
    cancel (@iter_sseq A d) (@sseq_iter _ _).
  Proof.
    elim : d =>[|d IH]//= x /=. rewrite sseqn_unlift_lift -sseqn_map_comp.
    rewrite (@eq_sseqn_map _ _ _ _ id); [exact /sseqn_map_id|exact /IH].
  Qed.

  Lemma sseq_iter_sseq (A:Type) (d:nat):
    cancel (@sseq_iter A d) (@iter_sseq _ _).
  Proof.
    elim : d =>[|d IH]//= x /=; [exact /to_from_sseq0|].
    rewrite -sseqn_map_comp (@eq_sseqn_map _ _ _ _ id); [|exact /IH].
      by rewrite sseqn_map_id sseqn_lift_unlift.
  Qed.

  Definition sseqNil (A:Type) : sseq A := sseqnNil _ 0.
  Definition sseqCons (A:Type) : A -> sseq (sseq A) -> sseq A :=
    fun a s => sseqnCons (to_sseq0 a) (sseqn_lift s).

  Lemma sseq_case (A:Type) (s:sseq A) :
    s = sseqNil _ \/ exists a s', s = sseqCons a s'.
  Proof.
    case : s =>[[[]|[] tl tr /=[xl xr]]]; [by left|right].
    exists (from_sseq0 (existT _ tl xl)),
    (@sseqn_unlift _ 1 _ (existT _ tr xr)). rewrite /sseqCons to_from_sseq0.
      by rewrite sseqn_lift_unlift.
  Qed.

  Variant sseq_or (A:Type) : sseq A -> Prop :=
  | SseqOrNil : sseq_or (sseqNil _)
  | SseqOrCons x s : sseq_or (sseqCons x s).

  Lemma sseqP (A:Type) (s:sseq A) : sseq_or s.
  Proof.
      by case : (sseq_case s) =>[|[x][s']]->; constructor.
  Qed.

  Lemma sseqCons_inj (A:Type) (x x':A) (s s':sseq (sseq A)):
    sseqCons x s = sseqCons x' s' -> x = x' /\ s = s'.
  Proof.
    rewrite -(from_to_sseq0 x) -(from_to_sseq0 x') /sseqCons !to_from_sseq0.
    rewrite -(sseqn_unlift_lift s) -(sseqn_unlift_lift s') !sseqn_lift_unlift.
    case : (to_sseq0 x) (to_sseq0 x') =>[t p][t' p'].
    case : (sseqn_lift s) (sseqn_lift s') =>[tr xr][tr' xr'] H.
    case : H (H) => Ht Htr. move : Ht Htr p' xr' =><-<- p' xr' H.
    suff : (p, xr) = (p', xr') by case =>->->.
    apply /Eqdep_dec.inj_pair2_eq_dec : H => y y'.
      by case : (@bitree_eqP _ y y'); [left|right].
  Qed.

  Lemma sseqCons_injl (A:Type) (x x':A) (s s':sseq (sseq A)):
    sseqCons x s = sseqCons x' s' -> x = x'.
  Proof. by move =>/(@sseqCons_inj A)[]. Qed.

  Lemma sseqCons_injr (A:Type) (x x':A) (s s':sseq (sseq A)):
    sseqCons x s = sseqCons x' s' -> s = s'.
  Proof. by move =>/(@sseqCons_inj A)[]. Qed.

  Lemma sseq_neqcons (A:Type) (a:A) x: sseqCons a x <> sseqNil _.
  Proof.
    rewrite /sseqCons/sseqNil.
      by case : (to_sseq0 a) (sseqn_lift x) =>[t0 p0][t p][].
  Qed.

  Lemma sseq_ind' (A:Type) (P:forall d, sseqn A d.+1 -> Prop) :
    (forall d, P _ (sseqnNil A d)) ->
    (forall (a:sseqn A 0) (s:sseqn A 2),
        P _ s -> P _ (sseqnCons a s)) ->
    (forall d (a:sseqn A d.+1) (s:sseqn A d.+3),
        P _ a -> P _ s -> P _ (sseqnCons a s)) ->
    forall d (s:sseqn A d.+1), P _ s.
  Proof.
    move => Hnil Hcons0 Hcons d [t].
    elim : t d =>[|[] tl IHl tr IHr][|d]/=[]; try exact /Hnil.
    - move => a b. exact /(Hcons0 (existT _ _ a) (existT _ _ b))/IHr.
    - move => a b. exact : Hcons (IHl _ a) (IHr _ b).
  Qed.

  Lemma sseqn_unlift_map (A B:Type) (k d:nat) (f:A -> B) (x:sseqn A (k + d)):
    sseqn_unlift (sseqn_map f x) = sseqn_map (sseqn_map f) (sseqn_unlift x).
  Proof.
    case : x =>[t]/=. elim : t k =>[|[] tl IHl tr IHr][|k]//=[xl xr]/=.
    rewrite IHl IHr. case : (sseqn_unlift_rec xl) =>[tl' xl']/=.
      by case : (@sseqn_unlift_rec _ _ _ k.+2 xr) =>[tr' xr'].
  Qed.

  Lemma sseqn_map_lift (A B:Type) (k d:nat) (f:A -> B) (x:sseqn (sseqn A d) k):
    sseqn_map f (sseqn_lift x) = sseqn_lift (sseqn_map (sseqn_map f) x).
  Proof.
    case : x => t. elim : t k =>[|[] tl IHl tr IHr][|k]//=[xl xr].
    move : (IHl _ xl) (IHr _ xr) =>/=<-<-.
    case : (sseqn_lift_rec xl) =>[tl' xl']/=.
      by case : (sseqn_lift_rec xr) =>[tr' xr'].
  Qed.
(*
  Lemma sseq_iter_unlift (A:Type) (k d:nat) (x:sseqn A (k + d)):
    sseq_iter x = sseq_iter (sseqn_map (@sseq_iter _ _) (sseqn_unlift x)).
                                                           :sseqn (sseqn A d) k
 *)
  (*
  Lemma sseqn_lift_iter_d2 (A:Type) (d:nat) (x:sseqn A d.+2):
    sseqn_lift (sseq_iter x) =
    sseqn_map (@sseq_iter _ _) (@sseqn_unlift _ 2 _ x).
  Proof.
    apply /(canLR (@sseqn_lift_unlift _ _ _)). rewrite sseqn_unlift_map /=.

    case : x => t /=.
    elim /bitree_ltn_ind : t d =>[][|[] tl tr]//= IH [|d][xl xr].
    - 
      move : (IH _ (leq_maxr _ _) _ xr) =>/=.
      case : (@sseqn_unlift_rec _ _ _ 2 xr) =>[tr' xr'].
      case : tl xl IH =>/=[|[] xll xlr][].
      + move => IH.
    elim : t d =>[|[] tl IHl tr IHr]//=[|d][xl xr].
    - move : tl xl {IHl} =>[|[] tll tlr]//=[].
    - move : (IHr _ xr).


    move : 
    move : (IHr _ xr).
    case : (@sseqn_unlift_rec _ _ _ 1 xl).
    case : t =>[|[] tl tr]//=.
    move =>/=.
*)
(*
  Lemma sseqn_lift_iter (A:Type) (k d:nat) (x:sseqn A (k + d)):
    sseqn_lift x 

  Lemma sseqn_map_Cons (A B:Type) (d:nat) (f:A -> B)
        (a:sseqn A d) (x:sseqn A d.+2):
    sseqn_map f (sseqnCons a x) = sseqnCons (sseqn_map f a) (sseqn_map f x).
 *)
  (*
  Lemma sseqCons_sseq_iter (A:Type) (d:nat) (a:sseqn A d) (x:sseqn A d.+2):
    sseqCons (sseq_iter a) (sseq_iter x) = sseq_iter (sseqnCons a x).
  Proof.
    rewrite /sseqCons.


    case : a x =>[ta xa][tx xx]/=.
    move =>/=.

    rewrite /sseqCons/=. case : (@sseqn_unlift_rec _ _ _ 1 xx).
*)
  Lemma sseq_ind (A:Type) (P:forall d, sseq (iter _ d sseq A) -> Prop) :
    (forall d, P _ (sseqNil (iter _ d sseq A))) ->
    (forall (a:A) (s:sseq (sseq A)), P 1 s -> P 0 (sseqCons a s)) ->
    (forall d (a:sseq (iter _ d sseq A))
            (s:sseq (sseq (sseq (iter _ d sseq A)))),
                 P d a -> P d.+2 s -> P d.+1 (sseqCons a s)) ->
    forall d (s:sseq (iter _ d sseq A)), P _ s.
  Proof.
    move => Hnil Hcons0 Hcons d s. rewrite -[s](@iter_sseq_iter _ d.+1).
    apply /(@sseq_ind' _ (fun d x => P d (sseq_iter x)))
    =>[d'|a x /(Hcons0 (sseq_iter a))|d' a x Ha Hx].
    - exact /Hnil.
    -


      case : a x =>[tl xl][tr xr]/=. case : (sseqn_unlift_rec xl).
      rewrite /sseqnCons. case : a.

      move : (sseq_iter a) (sseq_iter x) (Hcons0 (sseq_iter a) _ Hx) => a' x'.
      rewrite /sseqnCons.
    suff : forall k (p:sseq_rec A k x), P (sseqn A k) (existT (sseq_rec A k) x p).
    move : 1. elim =>[|[] tl IHl tr IHr]/=[]; [exact /Hnil|].
*)
End SSeq.

Section SSeq'.

  Inductive sseqn' (A:Type) : nat -> Type :=
  | sseqn'0 : A -> sseqn' A 0
  | sseqn'Nil d: sseqn' A d.+1
  | sseqn'Cons d: sseqn' A d -> sseqn' A d.+2 -> sseqn' A d.+1.

  Definition sseqn'_case0 (A:Type) (P:sseqn' A 0 -> Prop) :
    (forall a, P (sseqn'0 a)) -> forall x: sseqn' A 0 , P x :=
    fun H x => match x with
               | sseqn'0 a => H a
               | sseqn'Nil d => fun i => False_ind True i
               | sseqn'Cons d l r => fun i => False_ind True i
               end.

  Definition sseqn'_caseS (A:Type) (P:forall d, sseqn' A d.+1 -> Prop) :
    (forall d, P _ (sseqn'Nil _ d)) ->
    (forall d (a:sseqn' A d) s, P _ (sseqn'Cons a s)) ->
    forall d (x:sseqn' A d.+1), P _ x :=
    fun Hnil Hcons d x => match x with
                        | sseqn'0 a => fun i => False_ind True i
                        | sseqn'Nil d => Hnil d
                        | sseqn'Cons d l r => Hcons d l r
                          end.

  Definition falseT (T:Type) : False -> T := fun x => match x with end.

  Definition sseqn'_def0 (A T:Type) (f:A -> T) : sseqn' A 0 -> T :=
    fun x => match x with
             | sseqn'0 a => f a
             | sseqn'Nil d' => falseT
             | sseqn'Cons d' l r => falseT
             end.

  Definition sseqn'_defS' (A T:Type) (d:nat):
    sseqn' A d.+1 -> T -> (sseqn' A d -> sseqn' A d.+2 -> T) -> T :=
    fun x => match x with
               | sseqn'0 a => falseT
               | sseqn'Nil d => fun fnil _ => fnil
               | sseqn'Cons d l r => fun _ fcons => fcons l r
               end.

  Definition sseqn'_defS (A T:Type) (d:nat) (t:T)
             (f:sseqn' A d -> sseqn' A d.+2 -> T) (x:sseqn' A d.+1) : T :=
    sseqn'_defS' x t f.

  Fixpoint sseqn'_sseqn (A:Type) (d:nat) (x:sseqn' A d) : sseqn A d :=
    match x with
    | sseqn'0 a => to_sseq0 a
    | sseqn'Nil d => sseqnNil _ _
    | sseqn'Cons d a s => sseqnCons (sseqn'_sseqn a) (sseqn'_sseqn s)
    end.

  Fixpoint sseq_rec_sseqn' (A:Type) (d:nat) (t:bitree unit) :
    sseq_rec A d t -> sseqn' A d :=
    match d,t return sseq_rec A d t -> sseqn' A d with
    | 0,BiLeaf => @sseqn'0 A
    | 0,BiNode _ _ _ => fun x => match x with end
    | _.+1,BiLeaf => fun => sseqn'Nil _ _
    | _.+1,BiNode _ _ _ =>
      fun x => sseqn'Cons (sseq_rec_sseqn' x.1) (sseq_rec_sseqn' x.2)
    end.

  Definition sseqn_sseqn' (A:Type) (d:nat) (x:sseqn A d) : sseqn' A d :=
    match x with
    | existT _ t => sseq_rec_sseqn' t
    end.

  Lemma sseqn_sseqn'_sseqn (A:Type) (d:nat):
    cancel (@sseqn_sseqn' A d) (@sseqn'_sseqn _ _).
  Proof.
    case => t. elim : t d =>[|[] tl IHl tr IHr][|d]//=[]//= l r.
    move : (IHl _ l) (IHr _ r). by rewrite /=/sseqnCons=>->->.
  Qed.

  Lemma sseqn'_sseqn_sseqn' (A:Type) (d:nat):
    cancel (@sseqn'_sseqn A d) (@sseqn_sseqn' _ _).
  Proof.
    elim =>[||d' a Ha s Hs]//=. rewrite /sseqnCons. move : Ha Hs.
      by case : (sseqn'_sseqn a) (sseqn'_sseqn s) =>[ta xa][ts xs]/=->->.
  Qed.

  Fixpoint sseqn'_lift (A:Type) (d k:nat)
    (x:sseqn' (sseqn' A d) k) : sseqn' A (k + d) :=
    match x with
    | sseqn'0 a => a:sseqn' A (0 + d)
    | sseqn'Nil _ => sseqn'Nil _ _
    | sseqn'Cons _ a s =>
      sseqn'Cons (sseqn'_lift a) (sseqn'_lift s)
    end.

  Fixpoint sseqn'_unlift (A:Type) (d k:nat) :
    sseqn' A (k + d) -> sseqn' (sseqn' A d) k :=
    match k with
    | 0 => @sseqn'0 (sseqn' A (0 + d))
    | k'.+1 =>
      let f:sseqn' A (k' + d).+1 ->

      fun x:sseqn' A (k' + d).+1 =>
        match x in (sseqn' _ m.+1)
              return sseqn' (sseqn' A d) k'.+1 with
        | sseqn'0 _ => falseT _
        | sseqn'Nil _ => sseqn'Nil _ _
        | sseqn'Cons _ a s =>
          sseqn'Cons (sseqn'_unlift (a:sseqn' A (k' + d)))
                     (sseqn'_unlift (s:sseqn' A (k'.+2 + d)))
        end
    end.
                          
                              match n + m with
                              | 0 => False -> sseqn' (sseqn' A d) k'.+1
                              | n.+1 => sseqn' (sseqn' A d) k'.+1
                              end
                        with
                        | sseqn'0 _ => @falseT _
                        | sseqn'Nil _ => sseqn'Nil _ _
                        | sseqn'Cons _ a s =>
                          sseqn'Cons (sseqn'_unlift a)
                                     (sseqn'_unlift (s:sseqn' A (k'.+2 + d)))
                        end
    end.
      @sseqn'_defS _ (sseqn' (sseqn' A d) k'.+1) (k' + d)
                 (sseqn'Nil _ _)
                 (fun a s => sseqn'Cons (sseqn'_unlift a)
                                        (sseqn'_unlift (s:sseqn' A (k'.+2 + d))))
    end.
      
    
  Definition sseq' : 
End SSeq'.
