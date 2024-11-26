From mathcomp
     Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ********************* *)
Lemma perm_cons2 (T:eqType) (x y:T) s: perm_eq (x :: y :: s) (y :: x :: s).
Proof. by rewrite -perm_rcons /= perm_cons perm_rcons. Qed.

Lemma perm_ind (T:eqType) (P:seq T -> seq T -> Prop) :
  P [::] [::] ->
  (forall u s t, P s u -> P u t -> P s t) ->
  (forall a s t, P s t -> P (a :: s) (a :: t)) ->
  (forall a b s, P [:: a, b & s] [:: b, a & s]) ->
  forall s t, perm_eq s t -> P s t.
Proof.
  move => Hnil Htrans Hcons Hcons2 s.
  have [n] := ubnP (size s).
  elim : n s =>[|n IHn][|a s]//=;
                       [by move =>_ t; rewrite perm_sym =>/perm_nilP->|].
  rewrite ltnS => Hs [/seq.permP /(_ predT)|b t]// Hperm.
  move : (perm_mem Hperm b) (Hperm).
  rewrite !in_cons eq_refl =>/=/orP[/eqP->|Hb _].
  - rewrite perm_cons =>/(IHn _ Hs). exact : Hcons.
  - apply : Htrans (Htrans _ _ _ (Hcons a _ _ (IHn _ Hs _ (perm_to_rem Hb)))
                           (Hcons2 _ _ _)) (Hcons _ _ _ (IHn _ _ _ _)).
    + rewrite /= size_rem //. by case : s Hs Hb {Hperm}.
    + rewrite -(perm_cons b). apply : perm_trans Hperm.
        by rewrite -perm_rcons /= perm_cons perm_rcons perm_sym perm_to_rem.
Qed.

Lemma perm_eqind (T:eqType) (S:Type) (f:seq T -> S) :
  (forall a s t, f s = f t -> f (a :: s) = f (a :: t)) ->
  (forall a b s, f [:: a, b & s] = f [:: b, a & s]) ->
  forall s t, perm_eq s t -> f s = f t.
Proof.
  move => Hcons Hcons2. by apply : perm_ind =>[|u s t->||].
Qed.


Lemma fcycle_mem_next (T:eqType) (f:T -> T) (s:seq T) (x:T):
  fcycle f s -> x \in s -> f x \in s.
Proof.
  move => Hs Hx. move : (next_cycle Hs Hx) =>/eqP->. by rewrite mem_next.
Qed.

Lemma fcycle_mem_iter (T:eqType) (f:T -> T) (s:seq T) (x:T) (n:nat):
  fcycle f s -> x \in s -> iter n f x \in s.
Proof.
  move => Hf Hx. elim : n =>[|n]//=. exact /fcycle_mem_next.
Qed.

Lemma traject_inv (T:eqType) (f g:T -> T) (x:T) (n:nat):
  cancel f g ->
  traject f x n = rev (traject g (g (iter n f x)) n).
Proof.
  move => Hgf. elim : n =>[|n IH]//=. by rewrite rev_cons Hgf -IH -trajectSr.
Qed.

Lemma fcycle_iter_size_head_cons (T:eqType) (f:T -> T) (s:seq T) (x:T):
  fcycle f (x :: s) -> iter (size s).+1 f x = x.
Proof.
  move =>/fpathE. by rewrite iterSr size_rcons trajectSr =>/rcons_inj[].
Qed.

Lemma fcycle_iter_size_head (T:eqType) (f:T -> T) (s:seq T) (x:T):
  fcycle f s -> iter (size s) f (head x s) = head x s.
Proof.
  case : s =>[|y s]//=. exact /fcycle_iter_size_head_cons.
Qed.

(*
*)
Lemma ufcycle_iter_head_lt (T:eqType) (f:T -> T) (s:seq T) (x:T) (n:nat):
   uniq (x :: s) -> fcycle f (x :: s) ->
  n <= size s -> iter n f x = x -> n = 0.
Proof.
  move =>/=/andP[Hx Hu]/fpathE. case : n =>[|n]//. rewrite iterSr /= size_rcons.
  rewrite trajectSr =>/rcons_inj[Hs Hxf] Hn.
  rewrite -(@nth_traject _ _ _ (size s)) // -Hs => H.
    by move : H (mem_nth (f x) Hn) Hx =>->->.
Qed.

Lemma ufcycle_iter_head (T:eqType) (f:T -> T) (s:seq T) (x:T) (n:nat):
  uniq (x :: s) -> fcycle f (x :: s) ->
  iter n f x = x -> exists k, n = k * (size s).+1.
Proof.
  rewrite [n](divn_eq _ (size s).+1) => Hu Hcyc Hx. exists (n %/ (size s).+1).
  elim : (n %/ (size s).+1) Hx =>[|m IH]; rewrite ?mul0n ?add0n ?mulSn -?addnA.
  - apply /(ufcycle_iter_head_lt Hu Hcyc). by rewrite -ltnS ltn_mod.
  - rewrite addnC iterD fcycle_iter_size_head_cons =>// /IH->. exact /addnC.
Qed.

Lemma rot1_traject (T:eqType) (f:T -> T) (x:T) (n:nat):
  fcycle f (traject f x n) -> rot 1 (traject f x n) = traject f (f x) n.
Proof.
  move =>/(fcycle_iter_size_head x). rewrite size_traject. case : n =>[|n]//=.
    by rewrite rot1_cons -trajectS trajectSr -iterS iterSr =>->.
Qed.


Fixpoint utraject (T:eqType) (f:T -> T) (x0 x:T) (n:nat):=
  if n is n'.+1 then x :: if x == x0 then [::] else utraject f x0 (f x) n'
  else [::].

Lemma trajectS_utraject (T:eqType) (f:T -> T) (x0 x:T) (n:nat):
  iter n f x \notin traject f x n ->
  utraject f (iter n f x) x n.+1 = traject f x n.+1.
Proof.
  move => H /=. congr cons.
  elim : n x H =>[|n IH]/= x; rewrite ?eq_refl // in_cons negb_or eq_sym.
  case : ifP =>//=_. by rewrite -iterS iterSr =>/IH->.
Qed.


Section Tppmark.
  Variable (T:finType).

  Lemma fcycle_traject_porbit (p: {perm T}) (x:T):
    fcycle p (traject p x #|porbit p x|).
  Proof.
    case def_n : #|_| =>[|n]//=. apply /fpathP. exists n.+1. rewrite trajectSr.
      by rewrite -iterSr -def_n iter_porbit.
  Qed.

  Lemma traject_porbit_inv (p: {perm T}) (x:T):
    traject (p^-1)%g x #|porbit (p^-1)%g x|
  = rotr 1 (rev (traject p x #|porbit p x|)).
  Proof.
    rewrite (traject_inv _ _ (@permKV _ p)) -rev_rot iter_porbit porbitV.
      by rewrite rot1_traject ?fcycle_traject_porbit.
  Qed.

  Lemma looping_traject_porbit (p: {perm T}) (x:T):
    looping p x #|porbit p x|.
  Proof.
    apply /loopingP => n. rewrite -porbit_traject -permX. apply /porbitP.
      by exists n.
  Qed.

  Lemma porbit_card1P (p: {perm T}) (x:T):
    reflect (#|porbit p x| = 1) (p x == x).
  Proof.
    apply /(iffP eqP) =>[Hx|/eqP/card1P[y Hy]]; [apply /eqP/card1P|].
    - exists x => y. case Hy : (y \in pred1 x); apply /porbitP.
      + exists 0. move : Hy. by rewrite expg0 perm1 =>/eqP.
      + case =>[n Hn]. move : Hn Hy =>->/eqP.
          by elim : n =>[|n IH]; rewrite ?expg0 ?perm1 // expgS permM Hx.
    - move : (mem_porbit p 1 x) (Hy x) (Hy (p x)). rewrite porbit_id expg1 =>->.
        by move =>/esym/eqP->/esym/eqP.
  Qed.

  Lemma mem_porbit_card1P (p: {perm T}) (x:T):
    p x == x -> forall (y:T), reflect (y = x) (y \in porbit p x).
  Proof.
    move => H y. apply /(iffP idP) =>[|->]; [|by rewrite porbit_id].
    move : H (porbit_id p x) =>/porbit_card1P/eqP/cards1P[x'->].
      by rewrite !in_set1 =>/eqP->/eqP.
  Qed.

  Lemma porbit_iter (p: {perm T}) (x:T) (n:nat):
    iter n p x = x -> exists k, n = k * #|porbit p x|.
  Proof.
    have : x :: behead (traject p x #|porbit p x|) = traject p x #|porbit p x|
      by case : #|porbit p x| (card_porbit_neq0 p x). move => H.
    move =>/(@ufcycle_iter_head _ _ (behead (traject p x #|porbit p x|)))[||k];
      rewrite ?H ?uniq_traject_porbit ?fcycle_traject_porbit =>//->. exists k.
    rewrite size_behead size_traject.
      by case : #|porbit p x| (card_porbit_neq0 p x).
  Qed.

  Lemma iter_porbitP (p: {perm T}) (x:T) (n:nat):
    reflect (exists k, n = k * #|porbit p x|) (iter n p x == x).
  Proof.
    apply /(iffP eqP) =>[|[k ->]]; [exact /porbit_iter|].
    elim : k =>[|k IH]//. by rewrite mulSn iterD IH iter_porbit.
  Qed.

  Lemma my_porbitPmin' (p: {perm T}) (x y:T):
    y \in porbit p x -> exists2 i, i < #|porbit p x| & y = (p ^+ i)%g x.
  Proof.
    move =>/porbitP[n ->]. rewrite [n](divn_eq _ #|porbit p x|) expgD permM.
    exists (n %% #|porbit p x|).
    - rewrite ltn_mod. by case : #|porbit p x| (card_porbit_neq0 p x).
    - elim : (n %/ #|porbit p x|) =>[|m IH]/=; [by rewrite mul0n expg0 perm1|].
      rewrite mulSn expgD permM. move : IH. by rewrite !permX iter_porbit.
  Qed.

  Lemma my_porbitPmin (p: {perm T}) (x y:T):
    y \in porbit p x ->
          exists2 i,
          i < #|porbit p x| /\ (forall k, k < i -> (p ^+ k)%g x != y)
                            & y = (p ^+ i)%g x.
  Proof.
    move =>/my_porbitPmin' =>[[i Hi ->]]. exists i; split =>// k Hk. apply /eqP.
    rewrite -(subnK (ltnW Hk)) addnC expgD permM !permX =>/esym/eqP.
    move =>/iter_porbitP[n]. rewrite -permX porbit_perm. case : n =>[/eqP|n].
    - rewrite mul0n subn_eq0. by case : (ltnP k i) Hk.
    - rewrite mulSn => Hik. move : Hik (leq_ltn_trans (leq_subr k _) Hi) =>->.
        by rewrite -ltn_subRL subnn.
  Qed.

  Lemma porbit_disjointP (p: {perm T}) (x y:T):
    reflect [disjoint (porbit p x) & (porbit p y)] (y \notin porbit p x).
  Proof.
    apply /(iffP idP) =>[Hy|]; [rewrite -setI_eq0|].
    - case : (@eqP _ (porbit p x :&: porbit p y) set0) =>// /eqP/set0Pn[z].
      rewrite in_setI -eq_porbit_mem porbit_sym =>/andP[/eqP-> Hy'].
        by move : Hy' Hy =>->.
    - case Hy : (y \in porbit p x) =>//. move : Hy. rewrite -eq_porbit_mem.
      move =>/eqP->/disjoint_setI0/(f_equal (fun s:{set T} => x \in s)).
        by rewrite setIid in_set0 porbit_id.
  Qed.

  Lemma tpermComm (x y z w:T):
    x != z -> x != w -> y != z -> y != w -> commute (tperm x y) (tperm z w).
  Proof.
    move => Hxz Hxw Hyz Hyw. apply /permP => a. rewrite !permM.
    case : (@eqP _ x a)
    =>[<-|/eqP Hx]; [by rewrite tpermL !(@tpermD _ z) 1?eq_sym // tpermL|].
    case : (@eqP _ y a)
    =>[<-|/eqP Hy]; [by rewrite tpermR !(@tpermD _ z) 1?eq_sym // tpermR|].
    rewrite (tpermD Hx Hy). by case : tpermP; rewrite tpermD.
  Qed.

  Lemma tpermCu (x y z:T) :
    x != z -> y != z ->
    (tperm x y * tperm x z)%g = (tperm y z * tperm x y)%g.
  Proof.
    move => Hxz Hyz. apply /permP => a. rewrite !permM.
    case : (@eqP _ y a) =>[<-|/eqP Hya]; [by rewrite tpermR !tpermL tpermD|].
    case : (@eqP _ x a) =>[<-|/eqP Hxa]; [rewrite tpermL|].
    - case : (@eqP _ x y) =>[->|/eqP Hxy]; [by rewrite tpermL tperm1 perm1|].
        by rewrite (tpermD Hxy) 1?eq_sym // (@tpermD _ y) 1?eq_sym // tpermL.
    - rewrite (tpermD Hxa Hya).
      case : (@eqP _ z a) =>[<-|/eqP Hza]; [by rewrite !tpermR|].
        by rewrite (@tpermD _ y) // !tpermD.
  Qed.


  (* single cycle -> perm *)
  Fixpoint rtoperm1_rec (x0:T) (s:seq T) : {perm T} :=
    if s is x :: s' then tperm x0 x * rtoperm1_rec x s' else 1.

  Fixpoint rtoperm1 (s:seq T) : {perm T} :=
    if s is x0 :: s' then rtoperm1_rec x0 s' else 1.

  Fixpoint toperm1_rec (x0:T) (s:seq T) : {perm T} :=
    if s is x :: s' then tperm x0 x * toperm1_rec x0 s' else 1.

  Fixpoint toperm1 (s:seq T) : {perm T} :=
    if s is x0 :: s' then toperm1_rec x0 s' else 1.

  Fixpoint irtoperm1_rec (x0:T) (s:seq T) : {perm T} :=
    if s is x :: s' then irtoperm1_rec x s' * tperm x0 x else 1.

  Fixpoint irtoperm1 (s:seq T) : {perm T} :=
    if s is x0 :: s' then irtoperm1_rec x0 s' else 1.

  Lemma toperm1_rec_rcons (x0:T) (s:seq T) (x:T):
    toperm1_rec x0 (rcons s x) = (toperm1_rec x0 s * tperm x0 x)%g.
  Proof.
      by elim : s =>[|y s IH]/=; rewrite ?mulg1 ?mul1g // IH mulgA.
  Qed.

  Lemma rtoperm1_rec_rcons_rcons (x0:T) (s:seq T) (x y:T):
    rtoperm1_rec x0 (rcons (rcons s x) y) =
    (rtoperm1_rec x0 (rcons s x) * tperm x y)%g.
  Proof.
      by elim : s =>[|z s IH]/= in x0 *; rewrite ?mulg1 // IH mulgA.
  Qed.

  Lemma rtoperm1_rec_rcons (x0:T) (s:seq T) (x:T):
    rtoperm1_rec x0 (rcons s x) = ((rtoperm1_rec x (rcons (rev s) x0))^-1)%g.
  Proof.
    elim : s =>[|y s IH]/= in x x0 *; rewrite ?mulg1 ?tpermV 1?tpermC // IH.
      by rewrite rev_cons rtoperm1_rec_rcons_rcons invMg tpermV.
  Qed.

  Lemma rtoperm1_rev (s:seq T): rtoperm1 (rev s) = ((rtoperm1 s)^-1)%g.
  Proof.
    case : s =>[|y [|z s]]/=; rewrite ?invg1 // lastI rev_rcons /= rev_cons.
      by rewrite rtoperm1_rec_rcons revK -lastI.
  Qed.

  Lemma toperm1_rec_rev (x0:T) (s:seq T):
    toperm1_rec x0 (rev s) = ((toperm1_rec x0 s)^-1)%g.
  Proof.
    apply /eqP. rewrite -eq_invg_sym eq_invg_mul. apply /eqP.
    elim : s =>[|x s IH]/=; rewrite ?mul1g // rev_cons toperm1_rec_rcons -mulgA.
      by rewrite (@mulgA _ (tperm x0 x)) tperm2 mul1g.
  Qed.

  Lemma rtoperm1_rec_toperm1_rec (xh xt:T) (s:seq T):
    xh != xt -> xh \notin s -> xt \notin s -> uniq s -> 
    rtoperm1_rec xh (rcons s xt) = (toperm1_rec xt (rev s) * tperm xh xt)%g.
  Proof.
    elim : s =>[|x s IH]/= in xh *; [by rewrite mulg1 mul1g|rewrite !in_cons].
    rewrite !negb_or rev_cons toperm1_rec_rcons !(@tpermC _ _ xt) => Hht.
    move =>/andP[Hhx Hh]/andP[Htx Ht]/andP[Hx Huniq]. rewrite IH 1?eq_sym //.
    rewrite -mulgA tpermCu 1?eq_sym // !(@tpermC _ x) !mulgA. congr (_ * _)%g.
    elim : s Hh Hx {Ht Huniq IH}=>[|y s IH]/=; [by rewrite mulg1 mul1g|].
    rewrite !in_cons !negb_or rev_cons =>/andP[Hhy Hh]/andP[Hxy Hx].
      by rewrite !toperm1_rec_rcons mulgA IH // -!mulgA tpermComm // eq_sym.
  Qed.

  Lemma rtoperm1_toperm1 (s:seq T): uniq s -> rtoperm1 s = toperm1 (rev s).
  Proof.
    case : s =>[|xh s]//=/andP[]. case : (lastP s) =>[|s' xt]//.
    rewrite mem_rcons in_cons negb_or rcons_uniq rev_cons rev_rcons /=.
    move =>/andP[Hht Hh]/andP[Ht Huniq]. rewrite toperm1_rec_rcons tpermC.
    exact /rtoperm1_rec_toperm1_rec.
  Qed.

  Lemma toperm1_rtoperm1 (s:seq T): uniq s -> toperm1 s = rtoperm1 (rev s).
  Proof. move => H. by rewrite rtoperm1_toperm1 ?revK // rev_uniq. Qed.


  Lemma irtoperm1_rec_rtoperm1_rec (x0:T) (s:seq T):
    (irtoperm1_rec x0 s * rtoperm1_rec x0 s)%g = 1%g.
  Proof.
    elim : s =>[|x s IH]/= in x0 *; rewrite ?mulg1 // -mulgA.
      by rewrite (@mulgA _ (tperm _ _)) tperm2 mul1g.
  Qed.

  Lemma irtoperm1_rtoperm1 (s:seq T): (irtoperm1 s * rtoperm1 s)%g = 1%g.
  Proof.
      by case : s =>[|x0 s]/=; rewrite ?mulg1 // irtoperm1_rec_rtoperm1_rec.
  Qed.

  Lemma rtoperm1_rec_irtoperm1_rec (x0:T) (s:seq T):
    (rtoperm1_rec x0 s * irtoperm1_rec x0 s)%g = 1%g.
  Proof.
    elim : s =>[|x s IH]/= in x0 *; rewrite ?mulg1 // -mulgA.
      by rewrite (@mulgA _ (rtoperm1_rec _ _)) IH mul1g tperm2.
  Qed.

  Lemma rtoperm1_irtoperm1 (s:seq T): (rtoperm1 s * irtoperm1 s)%g = 1%g.
  Proof.
      by case : s =>[|x0 s]/=; rewrite ?mulg1 // rtoperm1_rec_irtoperm1_rec.
  Qed.


  (* cycles -> perm *)
  Definition rtoperm (s:seq (seq T)) : {perm T} :=
    foldr (mulg \o rtoperm1 \o rev) 1%g s.
  Definition toperm (s:seq (seq T)) : {perm T} :=
    foldr (mulg \o toperm1) 1%g s.
  Definition irtoperm (s:seq (seq T)) : {perm T} :=
    foldr (mulg \o irtoperm1) 1%g s.


  Lemma rtoperm_rcons (s:seq (seq T)) (x:seq T):
    rtoperm (rcons s x) = (rtoperm s * rtoperm1 (rev x))%g.
  Proof.
      by elim : s =>[|y s IH]/=; rewrite ?mulg1 ?mul1g // IH mulgA.
  Qed.

  Lemma rtoperm_inv (s:seq (seq T)):
    ((rtoperm s)^-1)%g = rtoperm (rev (map rev s)).
  Proof.
    elim : s =>[|x s IH]/=; rewrite ?invg1 // rev_cons rtoperm_rcons -IH.
      by rewrite invMg revK rtoperm1_rev invgK.
  Qed.

  Lemma toperm_rtoperm (s:seq (seq T)): all uniq s -> toperm s = rtoperm s.
  Proof.
      by elim : s =>[|x s IH]//=/andP[/toperm1_rtoperm1->/IH->].
  Qed.

  Lemma irtoperm_rtoperm_inv (s:seq (seq T)):
    (rtoperm (rev (map rev s)) * irtoperm s)%g = 1%g.
  Proof.
    elim : s =>[|x s IH]/=; rewrite ?mulg1 // rev_cons rtoperm_rcons revK.
      by rewrite -mulgA (@mulgA _ (rtoperm1 x)) rtoperm1_irtoperm1 mul1g.
  Qed.

  Lemma rtoperm_irtoperm (s:seq (seq T)): rtoperm s = irtoperm s.
  Proof.
    apply /eqP. by rewrite eq_mulVg1 rtoperm_inv irtoperm_rtoperm_inv eq_refl.
  Qed.

  Lemma toperm1_irtoperm1 (s:seq T):
    uniq s -> toperm1 s = irtoperm1 s.
  Proof.
    move => H. move : H (@toperm_rtoperm [:: s]) (@rtoperm_irtoperm [:: s])
                        =>/=->/(_ (erefl _))<-.
      by rewrite !mulg1.
  Qed.

  Lemma irtoperm1_notin (s:seq T) (x:T) : x \notin s -> irtoperm1 s x = x.
  Proof.
    case : s =>[|x0 s]/=; rewrite ?perm1 // in_cons negb_or =>/andP[].
    elim : s =>[|y s IH]//= in x x0 *; rewrite ?perm1 // in_cons negb_or permM.
    move => Hx0 /andP[Hy /(IH _ _ Hy)->]. by rewrite tpermD // eq_sym.
  Qed.

  Lemma irtoperm1_in (p: {perm T}) (s:seq T) (x:T) :
    fcycle p s -> uniq s -> x \in s -> irtoperm1 s x = p x.
  Proof.
    rewrite (cycle_path x).
    case : s =>[|x0 s]//=/andP[/eqP Hlast Hs]/andP[Hx0 Huniq].
    rewrite in_cons =>/orP[/eqP->|].
    - case : s Hlast Hs Hx0 {Huniq} =>[|y s]/=; rewrite ?perm1 // permM.
      move =>_/andP[/eqP->_]/irtoperm1_notin/=->. exact /tpermL.
    - case : (@eqP _ x (last x0 s)) =>[->_|]; [rewrite Hlast|].
      + elim : s =>[|y s IH]/= in x0 {Hx0 Huniq Hs Hlast} *; rewrite ?perm1 //.
          by rewrite permM IH tpermR.
      + elim : s x0 Hs Huniq Hx0 {Hlast} =>[|y s IH]//= x0 /andP[/eqP Hpx0 Hp].
        rewrite permM !in_cons negb_or =>/andP[Hy Huniq]/andP[Hx0y Hx0] Hx.
        move =>/orP[/eqP Hxy|Hxs]. (*/IH->//].*)
        * case : s Hxy Hx Hp Hy Hx0 {IH Huniq} =>[|z s]//=->_/andP[/eqP->_] Hy.
          move : Hy (irtoperm1_notin Hy). rewrite permM !in_cons !negb_or.
          move =>/andP[Hyz _]->/andP[Hx0z _]. by rewrite tpermL tpermD.
        * rewrite IH // tpermD //.
          -- elim : s y Hp Hx0 Hxs Hx {Hy Hx0y Hpx0 IH Huniq} =>[|z s IH]//= y.
             rewrite !in_cons negb_or =>/andP[/eqP<- Hp]/andP[Hx0 Hx0s].
             move =>/orP[/eqP->|]; [|exact /IH].
             case : s Hp Hx0s {IH} =>[|w s]//=/andP[/eqP->_].
               by rewrite in_cons negb_or =>/andP[].
          -- by case : (@eqP _  y (p x)) Hpx0 Hxs Hx0 =>//->/perm_inj->->.
  Qed.

  Lemma irtoperm_notin (r:seq (seq T)) (x:T):
    ~~ has (mem^~ x) r -> irtoperm r x = x.
  Proof.
    elim : r =>[|s r IH]/=; rewrite ?perm1 // permM negb_or =>/andP[].
      by move =>/irtoperm1_notin->.
  Qed.

  Lemma irtoperm_in (p: {perm T}) (r:seq (seq T)) (x:T):
    all (fcycle p) r -> uniq (flatten r) -> has (mem^~ x) r ->
    irtoperm r x = p x.
  Proof.
    elim : r =>[|s r IH]//=/andP[Hcs Hcyc]. rewrite cat_uniq permM =>/and3P[].
    move => Hus /hasPn/= H Hur.
    case Hx : (x \in s); [rewrite (irtoperm1_in Hcs) //|].
    - rewrite irtoperm_notin //. apply /hasPn => s' Hs' /=. move : (H (p x)).
      rewrite (fcycle_mem_next Hcs Hx). case Hpx : (p x \in s') =>//. apply.
      apply /flattenP. by exists s'.
    - rewrite irtoperm1_notin ?Hx //=. exact /IH.
  Qed.


  (* perm -> cycles *)
  Fixpoint fromperm_rec (p: {perm T}) (r:seq (seq T)) (s:seq T) :
    seq (seq T) :=
    if s is x :: s'
    then if has (mem^~ x) r then fromperm_rec p r s'
         else if p x == x then fromperm_rec p r s'
              else fromperm_rec p (traject p x #|porbit p x| :: r) s'
    else r.

  Definition fromperm (p: {perm T}) : seq (seq T) :=
    fromperm_rec p [::] (enum T).

  (* another definition *)
  Fixpoint fromperm'_rec (p: {perm T}) (r:seq (seq T)) (s:seq T) :
    seq (seq T) :=
    if s is x :: s'
    then if has (mem^~ x) r then fromperm'_rec p r s'
         else if p x == x then fromperm'_rec p r s'
              else let e := traject p x #|porbit p x| in
                   e :: fromperm'_rec p (e :: r) s'
    else [::].

  Lemma fromperm_perm'_rec p r s:
    fromperm_rec p r s = rev (fromperm'_rec p r s) ++ r.
  Proof.
    elim : s =>[|x s IH]//= in r *. case : ifP =>//. case : ifP =>//.
      by rewrite IH rev_cons cat_rcons.
  Qed.


  Lemma allfcycle_fromperm_rec (p: {perm T}) (r:seq (seq T)) (s:seq T):
    all (fcycle p) r -> all (fcycle p) (fromperm_rec p r s).
  Proof.
    elim : s =>[|x s IH]//= in r *. case : ifP =>_ Hp; [exact /IH|].
    case : ifP =>_; apply /IH =>//=. by rewrite fcycle_traject_porbit.
  Qed.

  Lemma allfcycle_fromperm (p: {perm T}): all (fcycle p) (fromperm p).
  Proof. exact /allfcycle_fromperm_rec. Qed.

  Lemma uniq_fromperm_rec (p: {perm T}) (r:seq (seq T)) (s:seq T):
    all (fcycle p) r -> uniq (flatten r) ->
    uniq (flatten (fromperm_rec p r s)).
  Proof.
    elim : s =>[|x s IH]//= in r *=> Hcyc Hur.
    case : ifP =>[_|/negbT /hasPn H]; [exact /IH|].
    case : ifP => Hpx; apply /IH =>//=; rewrite ?fcycle_traject_porbit //.
    rewrite cat_uniq uniq_traject_porbit Hur andbT /=. apply /hasPn => y /= Hy.
    rewrite -porbit_traject. apply /porbitP =>[][n Hn].
    move : Hn Hy Hcyc =>->/flattenP[s' Hs' Hn]/allP/(_ _ Hs') Hps'.
    move : (mem_porbit p n x) (H _ Hs'). rewrite porbit_sym =>/porbitP[m->].
      by rewrite permX fcycle_mem_iter.
  Qed.

  Lemma uniq_fromperm (p: {perm T}) : uniq (flatten (fromperm p)).
  Proof. exact /uniq_fromperm_rec. Qed.

  Lemma fromperm_rec_drop (p: {perm T}) (r:seq (seq T)) (s:seq T):
    exists r', fromperm_rec p r s = r' ++ r.
  Proof.
    elim : s =>[|x s IH]/= in r *; [by exists [::]|].
    case : ifP =>_; [|case : ifP =>_]; try exact /IH.
    case : (IH (traject p x #|porbit p x| :: r)) => r' Hr'.
    exists (rcons r' (traject p x #|porbit p x|)). by rewrite Hr' cat_rcons.
  Qed.

  Lemma fromperm_rec_id (p: {perm T}) (r:seq (seq T)) (s:seq T) (x:T):
    all (fcycle p) r -> all (leq 2 \o size) r ->
    ~~ has (mem^~ x) (fromperm_rec p r s) -> (x \notin s) || (p x == x).
  Proof.
    elim : s =>[|y s IH]//= in r *=> Hcyc Hsize. rewrite in_cons. case : ifP.
    - case : (@eqP _ x y) =>[<-|_ _]; [|exact /IH].
      case : (fromperm_rec_drop p r s) => r' ->. rewrite has_cat negb_or =>->.
        by rewrite andbF.
    - case : ifP; case : (@eqP _ x y)=>[<-|]; [by move =>->; rewrite orbT| | |].
      + move =>_ _ _. exact /IH.
      + case : (fromperm_rec_drop p (traject p x #|porbit p x| :: r) s) => r'.
        move =>->. rewrite has_cat /= !negb_or -porbit_traject porbit_id /=.
          by rewrite andbF.
      + move =>_ Hy _. apply /IH; rewrite /= ?fcycle_traject_porbit // Hsize.
        rewrite andbT. apply : leq_trans (card_size _).
        rewrite -(eq_card (porbit_traject _ _)).
        case def_n : #|porbit p y| =>[|[|_]]//; move : def_n.
        * by move : (card_porbit_neq0 p y) =>/eqP.
        * move =>/porbit_card1P. by rewrite Hy.
  Qed.

  Lemma fromperm_id (p: {perm T}) (x:T):
    ~~ has (mem^~ x) (fromperm p) -> p x = x.
  Proof.
    move => H. move : (@fromperm_rec_id p [::] _ x (erefl _) (erefl _) H).
      by rewrite mem_enum =>/eqP.
  Qed.

  (* soundness of irtoperm & ifromperm *)
  Lemma irtoperm_fromperm : cancel fromperm irtoperm.
  Proof.
    move => p. apply /permP => x. case H : (has (mem^~ x) (fromperm p)).
    - exact : irtoperm_in (allfcycle_fromperm p) (uniq_fromperm p) H.
    - move : H =>/negbT H. rewrite (fromperm_id H). exact /irtoperm_notin.
  Qed.

  Lemma toperm_fromperm : cancel fromperm toperm.
  Proof.
    move => p. rewrite toperm_rtoperm ?rtoperm_irtoperm ?irtoperm_fromperm //.
    elim : (fromperm p) (uniq_fromperm p) =>[|x s IH]//=. rewrite cat_uniq.
      by move =>/and3P[->].
  Qed.



  (* exchanges *)
  Definition istperm : pred {perm T} :=
    fun p => [exists x, [exists y, p == tperm x y]].

  Lemma tperm_istperm (x y:T) : istperm (tperm x y).
  Proof.
    apply /existsP. exists x. apply /existsP. exists y. exact /eq_refl.
  Qed.


  Definition isexchanges : pred (seq {perm T}) := all istperm.

  Lemma isexchanges_cat (s t:seq {perm T}):
    isexchanges (s ++ t) = isexchanges s && isexchanges t.
  Proof. by rewrite /isexchanges all_cat. Qed.

  Fixpoint toexchanges1_rec (x0:T) (s:seq T) : seq {perm T} :=
    if s is x :: s' then tperm x0 x :: toexchanges1_rec x0 s' else [::].

  Definition toexchanges1 (s:seq T) : seq {perm T} :=
    if s is x0 :: s' then toexchanges1_rec x0 s' else [::].

  Definition toexchanges (s:seq (seq T)) : seq {perm T} :=
    flatten (map toexchanges1 s).


  Lemma toexchanges1_rec_isexchanges (x0:T) (s:seq T):
    isexchanges (toexchanges1_rec x0 s).
  Proof.
    elim : s =>[|x s IH]//=. by rewrite tperm_istperm IH.
  Qed.


  (* toexchanges is valid *)
  Lemma toexchanges1_isexchanges (s:seq T):
    isexchanges (toexchanges1 s).
  Proof.
    case : s =>[|x s]//=. exact : toexchanges1_rec_isexchanges.
  Qed.

  Lemma toexchange_isexchanges (s:seq (seq T)):
    isexchanges (toexchanges s).
  Proof.
    rewrite /toexchanges. elim : s =>[|x s IH]//=.
      by rewrite isexchanges_cat toexchanges1_isexchanges.
  Qed.


  Lemma toexchange1_rec_toperm1_rec (x0:T) (s:seq T):
    toperm1_rec x0 s = foldr mulg 1%g (toexchanges1_rec x0 s).
  Proof.
    elim : s =>[|x s IH]//=. by rewrite IH.
  Qed.

  Lemma toexchange1_toperm1 (s:seq T):
    toperm1 s = foldr mulg 1%g (toexchanges1 s).
  Proof.
    case : s =>[|x0 s]//=. exact /toexchange1_rec_toperm1_rec.
  Qed.

  Lemma toexchanges_toperm (s:seq (seq T)):
    toperm s = foldr mulg 1%g (toexchanges s).
  Proof.
    elim : s =>[|x s IH]//=. rewrite /toexchanges/= foldrE big_cat -!foldrE.
      by rewrite toexchange1_toperm1 IH.
  Qed.


  (* toexchanges \o fromperm is valid *)
  Lemma toexchange_fromperm_isexchanges (p: {perm T}):
    isexchanges (toexchanges (fromperm p)).
  Proof.
    exact /toexchange_isexchanges.
  Qed.


  (* soundness of toexchanges \o fromperm *)
  Lemma toexchanges_fromperm: cancel (toexchanges \o fromperm) (foldr mulg 1%g).
  Proof.
    move => p /=. by rewrite -toexchanges_toperm toperm_fromperm.
  Qed.



  Lemma fromperm1: fromperm 1 = [::].
  Proof.
    rewrite /fromperm. elim : (enum T) =>[|x s IH]//=.
      by rewrite perm1 eq_refl.
  Qed.


  (* norm *)
  Definition permnorm (p: {perm T}): nat :=
    \sum_(x <- fromperm p) (size x).-1.

  Lemma size_toexchanges1 (s:seq T): size (toexchanges1 s) = (size s).-1.
  Proof.
    case : s =>[|x0 s]//=. elim : s =>[|x s IH]//=. by rewrite IH.
  Qed.

(* size of toexchanges *)
  Lemma permnorm_size_toexchanges (p: {perm T}):
    permnorm p = size (toexchanges (fromperm p)).
  Proof.
    rewrite /permnorm/toexchanges.
    elim : (fromperm p) =>[|x s IH]/=; rewrite ?big_nil // big_cons size_cat.
      by rewrite size_toexchanges1 IH.
  Qed.

  Lemma permnorm1: permnorm 1 = 0.
  Proof. by rewrite permnorm_size_toexchanges fromperm1. Qed.


  Lemma iter_tperm_porbit_lt (p: {perm T}) (x y:T) (n:nat):
    y \notin porbit p x ->
    n < #|porbit p x| -> iter n (tperm x y * p)%g (p x) = iter n p (p x).
  Proof.
    move => Hy. elim : n =>[|n IH]//= Hn. rewrite IH 1?ltnW // permM.
    rewrite -iterSr tpermD //; apply /eqP =>/esym.
    - move =>/porbit_iter[[|k]]// H. move : Hn. rewrite H mulSn -ltn_subRL.
        by rewrite subnn.
    - move => H. move : Hy. by rewrite -H -permX mem_porbit.
  Qed.


  Lemma iter_tperm_porbit' (p: {perm T}) (x y:T) (n:nat):
    x \notin porbit p y -> #|porbit p y| = n ->
    iter n (tperm x y * p)%g x = y.
  Proof.
    case : n =>[_/eqP|n]; [by move : (card_porbit_neq0 p y) =>/negbTE->|].
    rewrite iterSr permM tpermL tpermC => Hx Hpy.
      by rewrite (iter_tperm_porbit_lt Hx) -?iterSr -Hpy // iter_porbit.
  Qed.

  Lemma iter_tperm_porbit (p: {perm T}) (x y:T):
    x \notin porbit p y -> iter #|porbit p y| (tperm x y * p)%g x = y.
  Proof.
    move => H. exact /iter_tperm_porbit'.
  Qed.

  Lemma porbit_tperm_notin (p: {perm T}) (x y:T):
    y \notin porbit p x ->
    porbit (tperm x y * p)%g x = porbit p x :|: porbit p y.
  Proof.
    move => Hy. apply /setP => t. rewrite in_setU.
    apply /(sameP idP)/(iffP idP) =>[|/porbitP[n ->]].
    - move =>/orP[]/my_porbitPmin[[|n] [Hn _]->];
        rewrite permX ?iterSr /=?porbit_id //; apply /porbitP.
      + exists (n.+1 + #|porbit p y|).
        rewrite permX -(iter_tperm_porbit_lt Hy) 1?ltnW // iterD.
          by rewrite iter_tperm_porbit 1?porbit_sym // iterSr permM tpermR.
      + exists #|porbit p y|. by rewrite permX iter_tperm_porbit // porbit_sym.
      + exists n.+1. rewrite permX iterSr permM tpermL tpermC.
          by rewrite iter_tperm_porbit_lt 1?ltnW 1?porbit_sym.
    - rewrite !permX. elim : n =>[|n IH]/=; rewrite ?porbit_id //.
      move : IH =>/orP[]/porbitP[k->]; rewrite permM; apply /orP.
      + case : (@eqP _ x ((p ^+ k)%g x)) =>[<-|/eqP Hx].
        * right. apply /porbitP. exists 1. by rewrite tpermL expg1.
        * left. apply /porbitP. exists k.+1. rewrite tpermD ?expgSr ?permM //.
          apply /eqP => Hyk. move : Hy =>/porbitP. apply. by exists k.
      + case : (@eqP _ y ((p ^+ k)%g y)) =>[<-|/eqP Hyy].
        * left. apply /porbitP. exists 1. by rewrite tpermR expg1.
        * right. apply /porbitP. exists k.+1. rewrite tpermD ?expgSr ?permM //.
          apply /eqP => Hxk. move : Hy. rewrite porbit_sym =>/porbitP. apply.
          by exists k.
  Qed.

  Lemma card_porbit_tperm_notin (p: {perm T}) (x y:T):
    y \notin porbit p x ->
    #|porbit (tperm x y * p)%g x| = #|porbit p x| + #|porbit p y|.
  Proof.
    move => Hyx. rewrite porbit_tperm_notin // cardsU.
    rewrite disjoint_setI0 ?cards0 ?subn0 //. exact /porbit_disjointP.
  Qed.

  Lemma mem_porbit_tperm (p: {perm T}) (x y:T):
    y != x -> y \in porbit (tperm x y * p) x = (y \notin porbit p x).
  Proof.
    move =>/eqP.
    case H : (y \notin porbit p x);
                   [by rewrite porbit_tperm_notin // in_setU porbit_id orbT|].
    move : H =>/negPn. rewrite porbit_sym =>/my_porbitPmin[[|n][]].
    - by rewrite expg0 perm1 =>_ _/esym.
    - rewrite expgS permM => Hn Hmin Hpy.
      case H : (y \in porbit (tperm x y * p) x) =>//. move : H =>/porbitP[m Hy].
      have Hx : x = ((tperm x y * p) ^+ n.+1)%g x.
      + rewrite expgS !permM tpermL [in LHS]Hpy.
        elim : n {Hpy}=>[|n IH]//= in Hn Hmin *. rewrite !expgSr !permM -IH.
        * rewrite tpermD // eq_sym -permM -expgS; [exact /Hmin|rewrite permX].
          apply /iter_porbitP =>[[[|k Hk]]]//.
          move : Hk (ltn_trans (leqnn _) Hn)=>->. rewrite mulSn -ltn_subRL.
            by rewrite subnn.
        * exact : ltn_trans Hn.
        * move => k Hk. apply /Hmin. exact /leqW.
      + rewrite (divn_eq m n.+1) in Hy =>/eqP Hyx.
        suff : y != ((tperm x y * p) ^+ (m %% n.+1))%g x.
        * move /negbTE<-. apply /esym/eqP. move : Hy.
          elim : (m %/ n.+1) =>[|k IH]//. rewrite mulSn -addnA expgD.
          by rewrite permM -Hx.
        * case : (m %% n.+1) (ltn_mod m n.+1) =>[|k]; [by rewrite expg0 perm1|].
          rewrite expgS !permM tpermL !ltnS leq0n => Hk.
          have ->: ((tperm x y * p) ^+ k)%g (p y) = (p ^+ k)%g (p y).
          -- elim : k =>[|k IH]//= in Hk *.
             rewrite !expgSr !permM IH ?tpermD //; [| |exact /ltnW].
             ++ move : (Hmin _ (leqW Hk)). by rewrite eq_sym expgS permM.
             ++ rewrite permX -iterSr. apply /eqP=>/esym/porbit_iter[[|i Hi]]//.
                move : Hi (ltn_trans Hk (ltn_trans (leqnn _) Hn)) =>->.
                  by rewrite mulSn -ltn_subRL subnn.
          -- rewrite permX -iterSr. apply /eqP=>/esym/porbit_iter[[|i Hi]]//.
             move : Hi (leq_ltn_trans Hk (ltn_trans (leqnn _) Hn)) =>->.
               by rewrite mulSn -ltn_subRL subnn.
  Qed.

  Lemma porbit_tperm_in (p: {perm T}) (x y:T):
    y \in porbit p x ->
          porbit (tperm x y * p)%g x :|: porbit (tperm x y * p) y = porbit p x.
  Proof.
    case : (@eqP _ y x) =>[->|/eqP Hyx Hy]; [by rewrite tperm1 mul1g setUid|].
    apply /esym. move : (@porbit_tperm_notin (tperm x y * p)%g x y).
    rewrite mulgA tperm2 mul1g mem_porbit_tperm // Hy. exact.
  Qed.

  Lemma card_porbit_tperm_in (p: {perm T}) (x y:T):
    y != x -> y \in porbit p x ->
                    #|porbit (tperm x y * p)%g x| + #|porbit (tperm x y * p) y|
  = #|porbit p x|.
  Proof.
    move => Hyx Hy. rewrite -(porbit_tperm_in Hy) cardsU.
    rewrite disjoint_setI0 ?cards0 ?subn0 //. apply /porbit_disjointP.
      by rewrite mem_porbit_tperm // Hy.
  Qed.

  Lemma porbit_tperm_eq (p: {perm T}) (x y z:T):
    z \notin porbit p x -> z \notin porbit p y ->
    porbit (tperm x y * p)%g z = porbit p z.
  Proof.
    rewrite ![z \in _]porbit_sym => Hx Hy. apply /setP => w.
    apply /(sameP idP)/(iffP idP) =>/porbitP[n ->]; apply /porbitP; exists n;
    elim : n =>[|n IH]//=; rewrite !expgSr !permM.
    - by rewrite -IH tpermD //;
                     apply /eqP => H; move : Hx Hy;rewrite H mem_porbit.
    - by rewrite IH tpermD //;
                 apply /eqP => H; move : Hx Hy;rewrite H mem_porbit.
  Qed.

  Lemma permnorm_perm_eqL (p: {perm T}) (r r':seq (seq T)) (s:seq T):
    perm_eq r r' ->
    \sum_(x <- fromperm_rec p r s) (size x).-1 =
    \sum_(x <- fromperm_rec p r' s) (size x).-1.
  Proof.
    elim : s =>[|x s IH]/= in r r' *=> Hperm; [exact /perm_big|].
    rewrite (perm_has _ Hperm).
    case : ifP =>_; [|case : ifP =>_]; apply /IH =>//. by rewrite perm_cons.
  Qed.

  Lemma permnorm_perm_eqR (p: {perm T}) (r:seq (seq T)) (s s':seq T):
    perm_eq s s' ->
    \sum_(x <- fromperm_rec p r s) (size x).-1 =
    \sum_(x <- fromperm_rec p r s') (size x).-1.
  Proof.
    move => H. move : H r.
    apply /(@perm_ind _ (fun s s' =>
                           forall r,
                             \sum_(x <- fromperm_rec p r s) (size x).-1 =
                             \sum_(x <- fromperm_rec p r s') (size x).-1))
    =>[|s1 s2 s3 H12 H23|x s1 s2 H12|x y s0]//= r; [by rewrite H12| |].
    - by case : ifP; [|case : ifP].
    - case : ifP; [|case : ifP]; rewrite ?orbT ?orbF -?porbit_traject //.
      + case : ifP =>//. by case : (x \in porbit p y).
      + rewrite porbit_sym =>_ _. apply /esym. case : ifP; [by rewrite orbT|].
        case : ifP; case : ifP=>//= Hx _ _.
        * move : Hx. rewrite -eq_porbit_mem =>/eqP Hxy.
          elim : s0 =>[|z s0 IH]/= in r *;
                        [by rewrite !big_cons !size_traject Hxy|].
          rewrite -!porbit_traject {1}Hxy.
          case : ifP; [|case : ifP =>_ _]; try by rewrite IH.
          rewrite (permnorm_perm_eqL _ _ (perm_cons2 _ _ _)) IH.
            by rewrite (permnorm_perm_eqL _ _ (perm_cons2 _ _ _)).
        * by apply /permnorm_perm_eqL/perm_cons2.          
  Qed.

  Lemma permnorm_eq_cat (p: {perm T}) (r r' r0:seq (seq T)) (s:seq T):
    flatten r ++ filter (fun x => p x == x) (enum T)
    =i flatten r' ++ filter (fun x => p x == x) (enum T) ->
    \sum_(x <- fromperm_rec p (r ++ r0) s) (size x).-1 =
    \sum_(x <- r) (size x).-1 +
    \sum_(x <- fromperm_rec p (r' ++ r0) s) (size x).-1 -
    \sum_(x <- r') (size x).-1.
  Proof.
    elim : s =>[|x s IH]/= in r r' *.
    - by rewrite !big_cat /= -addnBA ?leq_addr // addKn.
    - case : (@eqP _ (p x) x) =>[/eqP|/eqP/negbTE] Hpx;
                                  [by case : ifP; case : ifP =>_ _; apply /IH|].
      move => Hflatten. move : (Hflatten x). rewrite !mem_cat.
      have -> : x \in [seq x <- enum T | p x == x] = false
        by rewrite mem_filter Hpx. rewrite !orbF => Hfx.
      case : ifP =>[/hasP[t]|/hasPn H].
      + case : ifP =>[_ _ _|/hasPn H]; [exact /IH|rewrite mem_cat].
        case /orP =>[] Ht Hx;
                      [|by move : (H t);
                        rewrite mem_cat Ht Hx orbT =>/(_ (erefl _))].
        move : Hfx.
        have -> : (x \in flatten r)=>[|/esym]; [by apply /flattenP; exists t|].
        move =>/flattenP[t' Ht' Hx']. move : (H t'). rewrite mem_cat Ht' Hx' /=.
          by move =>/(_ (erefl _)).
      + case : ifP =>[/hasP[t']|_]; rewrite -cat_cons ?mem_cat.
        * move =>/orP[] Ht' Hx';
            [|by move : (H t'); rewrite mem_cat Ht' Hx' orbT =>/(_ (erefl _))].
          move : Hfx.
          have -> : x \in flatten r'; [by apply /flattenP; exists t'|].
          move =>/flattenP[t Ht Hx]. move : (H t). rewrite mem_cat Ht Hx /=.
            by move =>/(_ (erefl _)).
        * rewrite (IH _ (traject p x #|porbit p x| :: r')) =>[|y];
              [|by move : (Hflatten y); rewrite !mem_cat -!orbA =>->].
            by rewrite !big_cons /= -addnA addnC subnDA addnK.
  Qed.

  Lemma permnorm_tperm_notin_sub'
        (p: {perm T}) (x y:T) (r r' r0:seq (seq T)) (s:seq T):
    (forall z, z \in s -> ~~ has (mem^~ z) r ->
                     (z \notin porbit p x) && (z \notin porbit p y)) ->
    flatten r ++ filter (fun z => p z == z) (enum T)
    =i flatten r' ++ filter (fun z => (tperm x y * p)%g z == z) (enum T) ->
    \sum_(x <- fromperm_rec p (r ++ r0) s) (size x).-1 =
    \sum_(x <- r) (size x).-1 +
    \sum_(x <- fromperm_rec (tperm x y * p)%g (r' ++ r0) s) (size x).-1 -
    \sum_(x <- r') (size x).-1.
  Proof.
    elim : s =>[|z s IH]/= in r r' *;
                 [by rewrite !big_cat /= -addnBA ?leq_addr // addKn|].
    rewrite !has_cat => Hz H.
    case : ifP =>[|/negbT]; [|rewrite negb_or =>/andP[Hr /negbTE->]].
    - case Hr0 : (has (mem^~ z) r0); rewrite ?orbT ?orbF
      => Hzr; [by apply /IH =>// w Hw; apply /Hz; rewrite in_cons Hw orbT|].
      case : ifP
      => Hzr'; [by apply /IH =>// w Hw; apply /Hz; rewrite in_cons Hw orbT|].
      case : ifP
      => Hpz; [by apply /IH =>// w Hw; apply /Hz; rewrite in_cons Hw orbT|].
      move : (H z) =>/esym. rewrite !mem_cat mem_filter Hpz /= orbF.
      have ->/=: z \in flatten r by apply /flattenP; move : Hzr =>/hasP.
      move =>/flattenP[s0 Hs0]. by move : Hzr' =>/hasPn/(_ _ Hs0)/negbTE->.
    - case Hr' : (has (mem^~ z) r')=>/=.
      + case : ifP
        => Hpz; [by apply /IH =>// w Hw; apply /Hz; rewrite in_cons Hw orbT|].
        move : (H z). rewrite !mem_cat mem_filter Hpz orbF.
        have ->/=: z \in flatten r' by apply /flattenP; move : Hr' =>/hasP.
        move =>/flattenP[s0 Hs0]. by move : Hr =>/hasPn/(_ _ Hs0)/negbTE->.
      + case : (@eqP _ x z)
        =>[->|/eqP Hxz] in Hr Hz *;
            [by move : (Hz _ (mem_head _ _) Hr); rewrite porbit_id|].
        case : (@eqP _ y z)
        =>[->|/eqP Hyz] in Hr Hz *;
            [by move : (Hz _ (mem_head _ _) Hr); rewrite porbit_id andbF|].
        rewrite permM tpermD // -cat_cons.
        case : ifP
        => Hpz; [by apply /IH =>// w Hw; apply /Hz; rewrite in_cons Hw orbT|].
        move : (Hz _ (mem_head _ _) Hr) =>/andP[Hzx Hzy].
        rewrite (IH _ (traject (tperm x y * p)%g z #|porbit (tperm x y * p) z|
                       :: r')) =>[|w Hw|w]/=.
        * rewrite !big_cons !size_traject porbit_tperm_eq // -addnA -addnC.
            by rewrite  subnDA addnK.
        * rewrite negb_or =>/andP[_]. apply /Hz. by rewrite in_cons Hw orbT.
        * rewrite -catA mem_cat H !mem_cat -orbA -!porbit_traject.
            by rewrite porbit_tperm_eq.
  Qed.

  Lemma permnorm_tperm_notin_sub
        (p: {perm T}) (x y:T) (r r':seq (seq T)) (s:seq T):
    (forall z, z \in s -> ~~ has (mem^~ z) r ->
                     (z \notin porbit p x) && (z \notin porbit p y)) ->
    flatten r ++ filter (fun z => p z == z) (enum T)
    =i flatten r' ++ filter (fun z => (tperm x y * p)%g z == z) (enum T) ->
    \sum_(x <- fromperm_rec p r s) (size x).-1 =
    \sum_(x <- r) (size x).-1 +
    \sum_(x <- fromperm_rec (tperm x y * p)%g r' s) (size x).-1 -
    \sum_(x <- r') (size x).-1.
  Proof.
    move => Hz H.
      by rewrite -[r]cats0 (@permnorm_tperm_notin_sub' _ x y _ r') // !cats0.
  Qed.

  Lemma fromperm_rec_size_leq (p: {perm T}) (r:seq (seq T)) (s:seq T):
    \sum_(x <- r) (size x).-1 <= \sum_(x <- fromperm_rec p r s) (size x).-1.
  Proof.
    elim : s =>[|x s IH]//= in r *. case : ifP =>//_. case : ifP =>//_.
    apply : leq_trans (IH _). by rewrite big_cons leq_addl.
  Qed.

  Lemma permnorm_tperm_in (p: {perm T}) (x y:T):
    y != x -> y \in porbit p x -> permnorm p = (permnorm (tperm x y * p)).+1.
  Proof.
    rewrite /permnorm/fromperm =>/negbTE Hyx Hy.
    have H : perm_eq (enum T) (x :: y :: rem y (rem x (enum T))).
    - move : (@perm_to_rem _ x (enum T)). rewrite mem_enum =>/(_ (erefl _)).
      move =>/permPl->. rewrite perm_cons perm_to_rem //.
      have : y \in enum T by rewrite mem_enum. elim : (enum T) =>[|z s IH]//=.
      rewrite in_cons =>/orP[/eqP<-|/IH]; [by rewrite Hyx mem_head|].
      case : ifP =>[_/mem_rem|]//_. rewrite in_cons =>->. exact /orbT.
    - rewrite !(permnorm_perm_eqR _ _ H) /= !permM tpermL tpermR !orbF.
      rewrite -!porbit_traject mem_porbit_tperm; [|exact /negbT]. rewrite !Hy.
      case : ifP Hyx =>[/mem_porbit_card1P/(_ _ Hy)/eqP->|]//= Hpxx Hyx.
      case : ifP; case : ifP => Hpxy Hpyx.
      + have /iter_porbitP[]: iter 2 p x == x
            by move : Hpxy Hpyx =>/=/eqP->/eqP->; rewrite eq_refl.
        case
        =>[|[|k Hk]]//;
                    [rewrite mul1n
                     => Hpx; rewrite (@permnorm_tperm_notin_sub _ x y _ [::])
                                     =>/=[|z|z]|].          
        * by rewrite big_cons !big_nil size_traject addn0 subn0 -Hpx.          
        * move : Hy. by rewrite -eq_porbit_mem orbF -porbit_traject =>/eqP->_->.
        * rewrite cats0 mem_cat !mem_filter -porbit_traject -enumT mem_enum.
          rewrite permM.
          case : tpermP
          =>[->|->|]; [by rewrite porbit_id Hpyx|by rewrite Hy Hpxy|].
          case Hz: (z \in porbit p x) =>//. move : Hz =>/my_porbitPmin[].
          rewrite -Hpx =>[][|[|k]]//=[]; rewrite ?ltnS ?expg0 ?perm1 ?expg1 //.
          move =>_ _->_/eqP/negbTE. by rewrite Hpxy. 
        * suff : 2 < k.+2 * #|porbit p x| by rewrite -Hk.
        move : Hpxx =>/porbit_card1P.
        case : #|porbit p x| (card_porbit_neq0 p x) =>[|[|j]]//.
          by rewrite !mulnS !addSn addnS.
      + rewrite (@permnorm_tperm_notin_sub
                   _ x y _ [:: traject (tperm x y * p)%g y
                               #|porbit (tperm x y * p) y|])=>/=[|z|z].
        * rewrite !big_cons !big_nil !addn0 !size_traject.
          rewrite -(card_porbit_tperm_in _ Hy); [|exact /negbT].
          rewrite -subn1 -[_ - 1]addnBA ?lt0n ?card_porbit_neq0 // subn1.
          rewrite addnC addnA addnK.
          suff ->: #|porbit (tperm x y * p) x| = 1 by rewrite addn1.
          apply /porbit_card1P. by rewrite permM tpermL.
        * move : Hy. rewrite -eq_porbit_mem negb_or -porbit_traject /= andbT.
            by move =>/eqP->_->.
        * rewrite !cats0 !mem_cat -!porbit_traject -(porbit_tperm_in Hy).
          rewrite in_setU !mem_filter -enumT mem_enum /= permM.
          case : tpermP =>[->|->|]; rewrite ?porbit_id ?Hpyx ?orbT //.
          have /mem_porbit_card1P Hx: (tperm x y * p)%g x == x
            by rewrite permM tpermL. by move =>/Hx/negbTE->.
      + rewrite (@permnorm_tperm_notin_sub
                   _ x y _ [:: traject (tperm x y * p)%g x
                               #|porbit (tperm x y * p) x|])=>/=[|z|z].
        * rewrite !big_cons !big_nil !addn0 !size_traject.
          rewrite -(card_porbit_tperm_in _ Hy); [|exact /negbT].
          rewrite -subn1 -[_ - 1]addnBAC ?lt0n ?card_porbit_neq0 // subn1.
          rewrite -addnA addKn.
          suff ->: #|porbit (tperm x y * p) y| = 1 by rewrite add1n.
          apply /porbit_card1P. by rewrite permM tpermR.
        * move : Hy. rewrite -eq_porbit_mem negb_or -porbit_traject /= andbT.
            by move =>/eqP->_->.
        * rewrite !cats0 !mem_cat -!porbit_traject -(porbit_tperm_in Hy).
          rewrite in_setU !mem_filter -enumT mem_enum /= permM.
          case : tpermP =>[->|->|]; rewrite ?porbit_id ?Hpxy ?orbT //.
          have /mem_porbit_card1P Hx: (tperm x y * p)%g y == y
            by rewrite permM tpermR. move =>_/Hx/negbTE->. by rewrite orbF.
      + rewrite (@permnorm_tperm_notin_sub
                   _ x y _ [:: traject (tperm x y * p)%g y
                               #|porbit (tperm x y * p) y|;
                               traject (tperm x y * p)%g x
                               #|porbit (tperm x y * p) x|])=>/=[|z|z].
        * rewrite !big_cons !big_nil !addn0 !size_traject.
          rewrite -(card_porbit_tperm_in _ Hy); [|exact /negbT].
          rewrite addnC -subn1 -[_ - 1]addnBA ?lt0n ?card_porbit_neq0 // subn1.
          rewrite addnA subnDA addnK -addnBA ?leq_pred // -subn1.
            by rewrite subKn ?addn1 // lt0n card_porbit_neq0.
        * move : Hy. rewrite -eq_porbit_mem negb_or -porbit_traject /= andbT.
            by move =>/eqP->_->.
        * rewrite !cats0 !mem_cat -!porbit_traject -(porbit_tperm_in Hy).
          rewrite in_setU !mem_filter -enumT mem_enum /= permM.
          case : tpermP =>[->|->|Hzx Hzy]; rewrite ?porbit_id ?Hpxy ?orbT //.
          congr(_ || _). exact /orbC.
  Qed.

  Lemma permnorm_tperm_notin (p: {perm T}) (x y:T):
    y \notin porbit p x -> (permnorm p).+1 = permnorm (tperm x y * p).
  Proof.
    case : (@eqP _ y x) =>[->|/eqP/negbTE Hyx Hy]; [by rewrite porbit_id|].
    rewrite /permnorm/fromperm.
    have H : perm_eq (enum T) (x :: y :: rem y (rem x (enum T))).
    - move : (@perm_to_rem _ x (enum T)). rewrite mem_enum =>/(_ (erefl _)).
      move =>/permPl->. rewrite perm_cons perm_to_rem //.
      have : y \in enum T by rewrite mem_enum. elim : (enum T) =>[|z s IH]//=.
      rewrite in_cons =>/orP[/eqP<-|/IH]; [by rewrite Hyx mem_head|].
      case : ifP =>[_/mem_rem|]//_. rewrite in_cons =>->. exact /orbT.
    - rewrite !(permnorm_perm_eqR _ _ H) /= !permM tpermL tpermR !orbF.
      rewrite -!porbit_traject mem_porbit_tperm; [|exact /negbT].
      move : (Hy) =>/negbTE->/=.
      have ->: p x == y = false;
        [by apply /eqP => Hx; move : Hx Hy =><-/porbitP; apply; exists 1;
                          rewrite expg1|].
      have ->: p y == x = false;
        [by apply /eqP => Hx; move : Hx Hy; rewrite porbit_sym =><-/porbitP;
                          apply; exists 1; rewrite expg1|].
      case : ifP; case : ifP => Hpyy Hpxx.
      + have /iter_porbitP[]: iter 2 (tperm x y * p)%g x == x;
          [by move : Hpyy; rewrite /= !permM tpermL =>/eqP->; rewrite tpermR|].
        case
        =>[|[|k Hk]]//;
                 [rewrite mul1n
                  => Hpx; rewrite (@permnorm_tperm_notin_sub
                                     _ x y _
                                     [:: traject (tperm x y * p)%g x
                                         #|porbit (tperm x y * p) x|])
                                  =>/=[|z|z]|].
        * rewrite big_cons !big_nil add0n size_traject addn0 -Hpx subn1.
          rewrite prednK //.
          apply : leq_trans (fromperm_rec_size_leq _ _ _).
            by rewrite big_cons size_traject.
        * case : (@eqP _ z x)
          =>[->/mem_rem|/(mem_porbit_card1P Hpxx)->];
              [by move : (mem_rem_uniqF x (enum_uniq T)) =>->|].
          case : (@eqP _ z y)=>[->|/(mem_porbit_card1P Hpyy)->]//.
            by move : (mem_rem_uniqF y (rem_uniq x (enum_uniq T))) =>->.
        * rewrite cats0 mem_cat !mem_filter -porbit_traject -enumT mem_enum.
          rewrite permM /= (porbit_tperm_notin Hy) in_setU.
          case : tpermP
          =>[->|->|]; rewrite ?porbit_id ?Hpxx ?Hpyy ?orbT //.
          move =>/(mem_porbit_card1P Hpxx)/negbTE->/(mem_porbit_card1P Hpyy).
            by move =>/negbTE->.
        * suff : 2 < k.+2 * #|porbit (tperm x y * p) x| by rewrite -Hk.
          case : #|porbit (tperm x y * p) x|
          (card_porbit_neq0 (tperm x y * p) x)
            (@porbit_card1P (tperm x y * p) x)
          =>[|[_ H1|j]]//; [|by rewrite !mulnS !addSn addnS].
          move : (erefl 1) =>/H1. rewrite permM tpermL.
            by move : Hpyy Hyx =>/eqP->->.
      + rewrite (@permnorm_tperm_notin_sub
                                     _ x y _
                                     [:: traject (tperm x y * p)%g x
                                         #|porbit (tperm x y * p) x|])
                =>/=[|z|z].
        * rewrite !big_cons !big_nil !size_traject (card_porbit_tperm_notin Hy).
          rewrite !addn0 (porbit_card1P _ _ Hpxx) /=.
          rewrite -subSn -?addSn ?prednK ?addKn // ?lt0n ?card_porbit_neq0 //.
          rewrite -subn1 -addnABC ?leq_addr // ?lt0n ?card_porbit_neq0 //.
          rewrite -lt0n. apply : leq_trans (fromperm_rec_size_leq _ _ _).
          rewrite big_cons big_nil addn0 /= size_traject ?lt0n.
            exact /card_porbit_neq0.
        * case : (@eqP _ z x)
          =>[->/mem_rem|/(mem_porbit_card1P Hpxx)->];
              [by move : (mem_rem_uniqF x (enum_uniq T)) =>->|].
            by rewrite orbF porbit_traject.
        * rewrite !cats0 !mem_cat -!porbit_traject (porbit_tperm_notin Hy).
          rewrite in_setU !mem_filter -enumT mem_enum /= permM.
          case : tpermP =>[->|->|]; rewrite ?porbit_id ?Hpxx ?orbT //.
            by move =>/(mem_porbit_card1P Hpxx)/negbTE->.
      + rewrite (@permnorm_tperm_notin_sub
                                     _ x y _
                                     [:: traject (tperm x y * p)%g x
                                         #|porbit (tperm x y * p) x|])
                =>/=[|z|z].
        * rewrite !big_cons !big_nil !size_traject (card_porbit_tperm_notin Hy).
          rewrite !addn0 (porbit_card1P _ _ Hpyy) addn1 /=.
          rewrite -subSn -?addSn ?prednK ?addKn // ?lt0n ?card_porbit_neq0 //.
          rewrite -subn1 -addnABC ?leq_addr // ?lt0n ?card_porbit_neq0 //.
          rewrite -lt0n. apply : leq_trans (fromperm_rec_size_leq _ _ _).
          rewrite big_cons big_nil addn0 /= size_traject ?lt0n.
            exact /card_porbit_neq0.
        * case : (@eqP _ z y)
          =>[->|/(mem_porbit_card1P Hpyy)->];
              [by move : (mem_rem_uniqF y (rem_uniq x (enum_uniq T))) =>->|].
            by rewrite orbF porbit_traject andbT.
        * rewrite !cats0 !mem_cat -!porbit_traject (porbit_tperm_notin Hy).
          rewrite in_setU !mem_filter -enumT mem_enum /= permM.
          case : tpermP =>[->|->|]; rewrite ?porbit_id ?Hpyy ?orbT //.
          move =>_/(mem_porbit_card1P Hpyy)/negbTE->. by rewrite orbF.
      + rewrite (@permnorm_tperm_notin_sub
                                     _ x y _
                                     [:: traject (tperm x y * p)%g x
                                         #|porbit (tperm x y * p) x|])
                =>/=[|z|z].
        * rewrite !big_cons !big_nil !size_traject (card_porbit_tperm_notin Hy).
          have ->: (#|porbit p x| + #|porbit p y|).-1 =
          (#|porbit p y|.-1 + #|porbit p x|.-1).+1
            by rewrite -subn1 -addnBAC ?lt0n ?card_porbit_neq0 // subn1 addnC
            -addSn prednK // lt0n card_porbit_neq0.
          rewrite addn0 -subSn -1?addSn ?addn0 ?addKn // addSn -addn1 leq_add2l.
          apply : leq_trans (fromperm_rec_size_leq _ _ _). rewrite big_cons.
          rewrite size_traject big_nil addn0 -subn1 -ltn_subCr subn0 -addn1.
            by apply /leq_add; rewrite lt0n card_porbit_neq0.
        * by rewrite orbF negb_or !porbit_traject andbC.
        * rewrite !cats0 !mem_cat -!porbit_traject (porbit_tperm_notin Hy).
          rewrite setUC in_setU !mem_filter -enumT mem_enum /= permM.
            by case : tpermP =>[->|->|]; rewrite ?porbit_id ?orbT //.
  Qed.
    

  Lemma permnorm_tperm (p: {perm T}) (x y:T):
    permnorm p <= (permnorm (tperm x y * p)).+1.
  Proof.
    case : (@eqP _ y x) =>[->|/eqP Hxy]; [by rewrite tperm1 mul1g|].
    case Hy : (y \in porbit p x).
    - by rewrite (permnorm_tperm_in Hxy Hy).
    - move : Hy =>/negbT/permnorm_tperm_notin<-. by rewrite !leqW.
  Qed.

(* toexchanges is minimam *)
  Lemma toexchanges_min (p: {perm T}) (s:seq {perm T}):
    isexchanges s -> foldr mulg 1%g s = p ->
    size (toexchanges (fromperm p)) <= size s.
  Proof.
    rewrite -permnorm_size_toexchanges.
    elim : s =>[|xy s IH]/= in p *; [by move =>_<-; rewrite permnorm1|].
    move =>/andP[/existsP[x /existsP[y /eqP->]] Hs]
         /(f_equal (mulg (tperm x y))). rewrite mulgA tperm2 mul1g =>/(IH _ Hs).
    rewrite -ltnS. by apply /leq_trans/permnorm_tperm.
  Qed.

End Tppmark.
