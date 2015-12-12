(*--build-config 
  options:--admit_fsi FStar.Set ;
  other-files: set.fsi heap.fst Flame_FLAM.fst;
--*)
module Flame.IFC

open Flame.FLAM

open FStar.Heap
open FStar.ST
open FStar.Set

kind STPre = STPre_h heap
kind STPost (a:Type) = STPost_h heap a
kind STWP (a:Type) = STWP_h heap a
new_effect STATE = STATE_h heap

kind IFCPre (context:Type) = STPre_h context
kind IFCPost (context:Type) (a:Type) = STPost_h context (result a)
kind IFCWP (context:Type) (a:Type) = STWP_h context (result a)

type toWP (#context:Type) (#a:Type) (pre:IFCPre context) (post: (context -> IFCPost context a)) =
    (fun (p:IFCPost context a) (c:context) -> pre c /\ (forall (r:result a) c1. (pre c /\ post c r c1) ==> p r c1))

type toWLP (#context:Type) (#a:Type) (pre:IFCPre context) (post: (context -> IFCPost context a)) =
    (fun (p:IFCPost context a) (c:context) -> (forall (r:result a) c1. (pre c /\ post c r c1) ==> p r c1))

type p_rec = (tc:trust_config * h:heap)
type p_pre (tc:trust_config) : (p_rec -> Type) = (fun prec -> subset tc (fst prec) == true)
type p_post (#a:Type) (tc:trust_config) = (fun (prec0:p_rec) x (prec1:p_rec) -> subset tc (fst prec0) == true)
type p_wp (#a:Type) (tc:trust_config) = (toWP #p_rec (p_pre tc) (p_post tc))
type p_wlp (#a:Type) (tc:trust_config) = (toWLP #p_rec (p_pre tc) (p_post tc))

type c_rec = (tc:trust_config * pc:prin * h:heap)
let getTC (crec:c_rec) : trust_config = let (tc,_,_) = crec in tc
let getPC (crec:c_rec) : prin  = let (_,pc,_) = crec in pc
let getHeap (crec:c_rec) : heap = let (_,_,h) = crec in h
type c_pre (tc:trust_config) : (c_rec -> Type) = (fun crec -> subset tc (getTC crec) == true)
type c_post (#a:Type) (tc:trust_config) (pc:prin) = 
  (fun (crec0:c_rec) x (crec1:c_rec) -> subset tc (getTC crec0) /\ flowsto tc (getPC crec0) pc)
type c_wp (#a:Type) (tc:trust_config) (pc:prin) = (toWP #c_rec (c_pre tc) (c_post tc pc))
type c_wlp (#a:Type) (tc:trust_config) (pc:prin) = (toWLP #c_rec (c_pre tc) (c_post tc pc))

type t_rec = {tc:trust_config; pc:prin; lbl:prin; h:heap}
let mktrec (crec:c_rec) (lbl:prin) = {tc = getTC crec; pc= getPC crec; lbl=lbl; h=getHeap crec}

type t_pre (tc:trust_config) (pc:prin) : (t_rec -> Type) = 
  (fun trec -> subset tc trec.tc /\ flowsto tc trec.pc pc)
type t_post (#a:Type) (tc:trust_config) (pc:prin) (lbl:prin) = 
  (fun trec0 x trec1 -> subset tc trec0.tc /\ flowsto tc trec0.pc pc /\ flowsto tc trec0.lbl lbl)
type t_wp (#a:Type) (tc:trust_config) (pc:prin) (lbl:prin) = (toWP #t_rec #a (t_pre tc pc) (t_post tc pc lbl))
type t_wlp (#a:Type) (tc:trust_config) (pc:prin) (lbl:prin) = (toWLP #t_rec #a (t_pre tc pc) (t_post tc pc lbl))

kind AllPre = AllPre_h t_rec
kind AllPost (a:Type) = AllPost_h t_rec a
kind AllWP (a:Type) = AllWP_h t_rec a
new_effect ALL = ALL_h t_rec
default effect ML (a:Type) =
  ALL a (all_null_wp t_rec a) (all_null_wp t_rec a)

new_effect TRUST = STATE_h p_rec
new_effect CTL = STATE_h c_rec
new_effect DEP = STATE_h t_rec
effect P (tc:trust_config) (a:Type) = TRUST a (p_wp tc) (p_wlp tc)
effect C (tc:trust_config) (pc:prin) (a:Type) = CTL a (c_wp tc pc) (c_wlp tc pc)
effect T (tc:trust_config) (pc:prin) (lbl:prin) (a:Type) = DEP a (t_wp tc pc lbl) (t_wlp tc pc lbl)

sub_effect
  STATE ~> TRUST = fun (a:Type) (wp:STWP a) (p:IFCPost p_rec a) (prec:p_rec) 
		  -> (wp (fun a h -> p a prec)) (snd prec)
sub_effect
  EXN ~> TRUST = fun (a:Type) (wp:ExWP a) (p:IFCPost p_rec a) (prec:p_rec) -> wp (fun ra -> p ra prec)

//sub_effect
//  PURE ~> TRUST = fun (a:Type) (wp:PureWP a) (p:IFCPost p_rec a) (prec:p_rec) -> wp (fun a -> p (V a) prec)
//
//(* for termination sensitivity, could do something different here? *)
//sub_effect
//  DIV ~> TRUST = fun (a:Type) (wp:PureWP a) (p:IFCPost p_rec a) (prec:p_rec) -> wp (fun a -> p (V a) prec)


sub_effect
  TRUST ~> CTL = fun (a:Type) (wp:IFCWP p_rec a) (p:IFCPost c_rec a) (crec:c_rec) 
		  -> (wp (fun a prec -> p a crec)) ((getTC crec), (getHeap crec))
sub_effect
  CTL ~> DEP = fun (a:Type) (wp:IFCWP c_rec a) (p:IFCPost t_rec a) (trec:t_rec) 
		  -> (wp (fun a crec -> p a (mktrec crec trec.lbl))) (trec.tc,trec.pc,trec.h)
//sub_effect
//  DEP ~> ALL = fun (a:Type) (wp:IFCWP t_rec a) (p:AllPost a) -> wp (fun a -> p a)

// monadic effect lattice?
// DIV ~> STATE ~> P ~> C ~> T ~> ALL
// DIV ~> EXN ~> P ~> C ~> T ~> ALL
// DIV ~> A ~> T ~> ALL
(*
//effect M (tc:trust_config) (pc:prin) (l:prin) (a:Type) = P tc (C tc pc (T tc pc l)) 
val t_return : #a:Type -> tc:trust_config -> pc:prin -> l:prin -> x:a -> T tc pc l a
let t_return (#a:Type) tc pc l x trec0 = (x, {tc=tc;pc=pc;lbl=l;h=trec0.h})

val c_return : #a:Type -> tc:trust_config -> pc:prin -> #l:prin -> x:T tc pc l a -> Tot (C tc pc (T tc pc l a))
let c_return (#a:Type) tc pc l x pc0 = (x, (tc,pc))

val p_return : #a:Type -> tc:trust_config -> #pc:prin -> #l:prin -> x:C tc pc (T tc pc l a) -> Tot (P tc (C tc pc (T tc pc l a)))
let p_return (#a:Type) tc pc l x l0 = (x, tc)

val return : #a:Type -> tc:trust_config -> pc:prin -> l:prin -> x:a -> Tot (M tc pc l a)
let return (#a:Type) tc pc l x = p_return tc (c_return tc pc (t_return tc pc l x))

type A (p:prin) (q:prin) = 
  IFC (prin * prin) unit (fun pq -> p==(fst pq) /\ q==(snd pq)) (fun pq0 x pq1 -> p==(fst pq0) /\ q==(snd pq0))
val del : p:prin -> q:prin -> Tot (A p q) 
let del p q _ = ((), (p, q)) 

assume val t_bind : #a:Type -> #b:Type -> #tc:trust_config -> #pc:prin -> #l:prin -> #l':prin
            -> f:T tc pc l a{flowsto tc (join pc l) l'}
            -> g: (x:a -> Tot (T tc pc l' b))
            -> Tot (T tc pc l' b)

assume val c_bind : #a:Type -> #b:Type -> #tc:trust_config -> #pc:prin -> #pc':prin
            -> f:C tc pc a{flowsto tc pc pc'}
            -> g: (x:a -> Tot (C tc pc' b))
            -> Tot (C tc pc b)

assume val p_bind : #a:Type -> #b:Type -> #tc:trust_config -> #tc':trust_config 
            -> f:P tc a
            -> g: (x:a -> Tot (P tc b))
            -> Tot (P tc b)

assume val bind : #a:Type -> #b:Type -> #tc:trust_config -> #pc:prin -> #l:prin 
            -> #pc':prin
	    -> #l':prin
            -> f:M tc pc l a
            -> g: (x:a -> Tot (M tc pc' l' b)){flowsto tc (join pc l) pc' /\ flowsto tc l l'}
            -> Tot (M tc pc l' b)

assume val authorize : #a:Type -> #b:Type -> #tc:trust_config -> #tc':trust_config -> #pc:prin -> #l:prin 
            -> #pc':prin -> #l':prin -> #p:prin -> #q:prin
            -> d:M tc pc l (A p q) 
            -> g:(x:unit -> Tot (M (add tc' (p,q,pc,l)) (join pc l) l' b)){
	     // the premises of FLAC's assume
	     actsfor tc l (voice q)
	     /\  actsfor tc pc (voice q)
	     /\  actsfor tc (voice p) (voice q)
	     /\  flowsto tc l l'}
            -> Tot (M tc pc l' b)

(* sanity checks for return *)
let return_test0 tc pc l x = (return empty pc l x) tc 
//let return_test1 tc pc l x = (p_return tc pc l x) tc 
// any computation can run in a pc' that flows to pc
//let return_test2 tc pc l x (pc':prin{flowsto empty pc' pc}) l' = (return tc pc l x) empty

// negative test: the converse of test2 is not true
//let return_test3 pc l x (pc':prin) l' = (c_return pc (t_return l x)) pc'
// negative test: can't run in a secret pc
//let return_test4 pc l x (pc':prin) l' = (c_return pc (t_return l x)) pc'

(* sanity checks for bind *)
// using a value x raises the pc 
//let bind_test0 tc pc l x = bind (return tc pc l x) (fun y -> return tc (join pc l) l y)

// a public and trusted pc and l can be used in any computation
////let bind_test1 tc pc l x = bind (return tc flow_bot flow_bot x) (fun y -> return tc pc l y)

// a public and trusted pc and l can be used in any computation (applied to bot context)
//let bind_test2 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_bot x) (fun y -> return pc l y) flow_bot

// a public and trusted pc with any label l that flows to l' can be used in a computation with any pc' and l'
//let bind_test6 l pc' (l':prin{l =<= l'}) x = bind (*flow_bot l pc' l'*) (return flow_bot l x) (fun y -> return pc' l' y) 

// negative test: flow_top doesn't (necessarily) flow to l
//let bind_test7 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_top x) (fun y -> return pc l y)
// negative test: 
//let bind_test8 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_bot x) (fun y -> return pc l y) flow_top

//val apply : #a:Type -> #b:Type -> #pc:prin -> #pc':prin
//            -> e:(a -> Tot (C pc' b)){pc =<= pc'}
//            -> e':C pc a
//            -> Tot (C pc b)
//let apply (#a:Type) (#b:Type) (#pc:prin) (#pc':prin) e e' = 
//  c_bind e' (fun x -> e x)
//
//type sum (a:Type) (b:Type) =
//  | L: a -> sum a b
//  | R: b -> sum a b
//
//val case : #a:Type -> #b:Type -> #c:Type -> #pc:prin -> #pc':prin
//	   -> e:(C pc (sum a b)){pc =<= pc'}   
//	   -> left:(a -> Tot (C pc' c))
//	   -> right:(b -> Tot(C pc' c)) -> Tot(C pc c)
//let case (#a:Type) (#b:Type) (#c:Type) (#pc:prin) (#pc':prin) 
//	 // this didn't type-check until I added the refinement to e.  
//	 //  -- why did I need it? (apply didn't require it)
//	 (e:C pc (sum a b){pc =<= pc'}) (left:(a -> Tot (C pc' c))) (right:(b -> Tot(C pc' c))) =
//  c_bind e (fun (x:sum a b) -> match x with | L xa -> left xa | R xb -> right xb)

(* If I could, I would create macros that rewrite:
      use x y z in e
to 
      bind x (fun x' -> bind y 
	    (fun y' -> bind z
	       (fun z' -> (fun x y z -> e) x' y' z')))
and
       c_match e with ...
to
       c_bind e (fun x -> match x with ...)
*)
  
(*
(**
 * Principal equivalence
 *)
Reserved Infix "==" (at level 70, no associativity).

Inductive prinEq : relation Prin :=
    (* Reflexive transitive symmetric closure *)
  | refl:  
  | symm:  forall p q,              q == p -> p == q
  | trans: forall p q r,  p == q -> q == r -> p == r

    (* Lattice commutativity laws *)
  | conjComm: forall p q,                 p ∧ q == q ∧ p
  | disjComm: forall p q,                 p ∨ q == q ∨ p

    (* Lattice associativity laws *)
  | conjAssoc: forall p q r,        (p ∧ q) ∧ r == p ∧ (q ∧ r)
  | disjAssoc: forall p q r,        (p ∨ q) ∨ r == p ∨ (q ∨ r)

    (* Lattice absorption laws *)
  | conjDisjAbsorb: forall p q,     p ∧ (p ∨ q) == p
  | disjConjAbsorb: forall p q,     p ∨ (p ∧ q) == p

    (* Lattice idempotence laws *)
  | conjIdemp: forall p,                  p ∧ p == p
  | disjIdemp: forall p,                  p ∨ p == p

    (* Lattice identity laws *)
  | conjIdent: forall p,                  p ∧ ⊥ == p
  | disjIdent: forall p,                  p ∨ ⊤ == p
  | conjTop:   forall p,                  p ∧ ⊤ == ⊤
  | disjBot:   forall p,                  p ∨ ⊥ == ⊥

    (* Lattice distributivity law *)
  | conjDistDisj:  forall p q r,    p ∧ (q ∨ r) == (p ∧ q) ∨ (p ∧ r)

    (* Authority projections, property 3: distribution over conjunctions *)
  | conjConf:    forall p q,           (p ∧ q)→ == p→ ∧ q→
  | conjInteg:   forall p q,           (p ∧ q)← == p← ∧ q←
  | ownDistConj: forall p q r,        (p ∧ q):r == p:r ∧ q:r

    (* Authority projections, property 4: distribution over disjunctions *)
  | disjConf:    forall p q,           (p ∨ q)→ == p→ ∨ q→
  | disjInteg:   forall p q,           (p ∨ q)← == p← ∨ q←
  | ownDistDisj: forall p q r,        (p ∨ q):r == p:r ∨ q:r

    (* Authority projections, property 5: idempotence *)
  | confIdemp:  forall p,                   p→→ == p→
  | integIdemp: forall p,                   p←← == p←
  | ownIdemp:   forall p q,             (p:q):q == p:q

    (* Basis projections, properties 2-3 *)
  | confInteg:      forall p,                p→← == ⊥
  | integConf:      forall p,                p←→ == ⊥
  | confDisjInteg:  forall p q,          p→ ∨ q← == ⊥

    (* Ownership projections, properties 3-6 *)
  | ownsSelf:    forall p,                  p:p == p
  | ownsBot:     forall p,                  p:⊥ == ⊥
  | conjDistOwn: forall p q r,        p:(q ∧ r) == p:q ∧ p:r
  | disjDistOwn: forall p q r,        p:(q ∨ r) == p:q ∨ p:r

    (* Ownership projections, property 7 *)
  | ownConfAssoc:  forall p q,             p:q→ == (p:q)→
  | ownIntegAssoc: forall p q,             p:q← == (p:q)←

    (* Ownership projections, property 8 *)
  | ownConf:  forall p q,                  p→:q == (p:q)→
  | ownInteg: forall p q,                  p←:q == (p:q)←

    (* Admitted equivalences *)
  | confIntegBasis: forall p,            p→ ∧ p← == p
  | botConf:                                  ⊥→ == ⊥
  | botInteg:                                 ⊥← == ⊥
  | botOwn:         forall p,                ⊥:p == ⊥

    (* Substitutions *)
  | conjSubst:  forall p p' q q', p == p' -> q == q' -> p ∧ q == p' ∧ q'
  | disjSubst:  forall p p' q q', p == p' -> q == q' -> p ∨ q == p' ∨ q'
  | confSubst:  forall p p',      p == p' ->               p→ == p'→
  | integSubst: forall p p',      p == p' ->               p← == p'←
  | ownsSubst:  forall p p' q q', p == p' -> q == q' ->   p:q == p':q'

where "p == q" := (prinEq p q).
*)
  *)
