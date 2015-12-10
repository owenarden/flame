(*--build-config
options:--admit_fsi FStar.Set;
other-files: set.fsi heap.fst st.fst all.fst;
--*)
module Flame

open FStar.All
open FStar.ST
open FStar.Set

kind IFCPre (context:Type) = STPre_h context
kind IFCPost (context:Type) (a:Type) = STPost_h context a

type IFC (context:Type) (a:Type) (pre:IFCPre context) (post: (context -> IFCPost context a)) =
  ctx0:context -> Pure (a * context) (pre ctx0) (fun actx -> post (snd actx) (fst actx) ctx0)

type prin =
  | Top : prin
  | Bot : prin
  | Name : str:string -> prin
  | Conj : left:prin -> right:prin -> prin
  | Disj : left:prin -> right:prin -> prin
  | Conf : p:prin -> prin 
  | Integ : p:prin -> prin 

val join : prin -> prin -> Tot prin
let join p q = (Conj (Conf (Conj p q)) (Integ (Disj p q))) 
val meet : prin -> prin -> Tot prin
let meet p q = (Conj (Conf (Disj p q)) (Integ (Conj p q))) 

type trust_config = set (p:prin * q:prin * pc:prin * l:prin)

//assume val actsfor : prin -> prin -> Tot bool
//let flowsto p q = actsfor (Conj (Conf q) (Integ p)) (Conj (Conf p) (Integ q))
//let flowsto p q = actsfor (Conj (Conf q) (Integ p)) (Conj (Conf p) (Integ q))

assume val flowsto : prin -> prin -> Tot bool
val equiv: prin -> prin -> Tot bool
let equiv p q = flowsto p q && flowsto q p 

val op_Equals_Greater_Less_Equals: prin -> prin -> Tot bool
let op_Equals_Greater_Less_Equals p q = flowsto p q && flowsto q p

val op_Equals_Less_Equals: prin -> prin -> Tot bool
let op_Equals_Less_Equals p q = flowsto p q 

val op_Equals_Greater_Equals: prin -> prin -> Tot bool
let op_Equals_Greater_Equals p q = flowsto q p 

type C (pc:prin) (a:Type) = IFC prin a (fun pc' -> pc' =<= pc == true) 
				       (fun pc0 x pc1 -> pc0 =<= pc == true)

type T (lbl:prin) (a:Type) = IFC prin a (fun lbl' -> True) 
					(fun lbl0 x lbl1 -> lbl0 =<= lbl == true)

type P (pi:trust_config) (a:Type) = IFC trust_config a (fun pi' -> subset pi pi' == true) 
					(fun pi0 x pi1 -> subset pi0 pi == true)

let flow_bot = (Integ Top)
let flow_top = (Conf Top)

assume TopPrin : forall (p:prin) . p =<= flow_top == true
assume BotPrin : forall (p:prin) . flow_bot =<= p == true
assume ReflPrin : forall (p:prin) (q:prin). p == q ==> p =<= q
assume SymmPrin : forall (p:prin) (q:prin). p =><= q ==> q =><= p
assume TransPrin : forall (p:prin) (q:prin) (r:prin). (p =<= q /\ q =<= r) ==> p =<= r

assume JoinIdem: forall (p:prin). {:pattern join p p} join p p == p  
assume JoinTop: forall (p:prin) . {:pattern join p flow_top} join p flow_top == flow_top 
assume JoinBot: forall (p:prin) . {:pattern join p flow_bot} join p flow_bot == p 
assume JoinComm: forall (p:prin) (q:prin). join p q == join q p

val c_return : #a:Type -> #l:prin -> pc:prin -> x:T l a -> Tot (C pc (T l a))
let c_return (#a:Type) (#l:prin) pc x pc0 = (x, pc)

val t_return : #a:Type -> l:prin -> x:a -> Tot (T l a)
let t_return (#a:Type) l x l0 = (x, l)

val return : #a:Type -> pc:prin -> l:prin -> x:a -> Tot (C pc (T l a))
let return pc l x = c_return (join pc l) (t_return l x)

assume val c_bind : #a:Type -> #b:Type -> #pc:prin -> #pc':prin
            -> f:C pc a{pc =<= pc'}
            -> g: (x:a -> Tot (C pc' b))
            -> Tot (C pc b)
//let c_bind (#a:Type) (#b:Type) (#pc:prin) (#pc':prin) (f:(C pc a){pc =<= pc'}) (g:(x:a -> Tot (C pc' b))) pc0 = let (x, pc) = f pc0 in g x pc

assume val bind : #a:Type -> #b:Type -> #pc:prin -> #l:prin 
            -> #pc':prin
	    -> #l':prin
            -> f:C pc (T l a)
            -> g: (x:a -> Tot (C pc' (T l' b))){(join pc l) =<= pc' /\ l =<= l'}
            -> Tot (C pc (T l' b))
//let l_bind (#a:Type) (#b:Type) (#pc:prin) (#l:prin) (#pc':prin) (#l':prin) f g pc0 l0 = 
//  let (lx, pc) = f pc0 in 
//    let (x, l) = lx l0 in g x pc l 

(* sanity checks for return *)
// any computation can run in a trusted pc
let return_test0 pc l x = (return pc l x) flow_bot 
// any computation can run in a pc' that flows to pc
let return_test2 pc l x (pc':prin{pc' =<= pc}) l' = (return pc l x) pc' 

// negative test: the converse of test2 is not true
//let return_test3 pc l x (pc':prin) l' = (c_return pc (t_return l x)) pc'
// negative test: can't run in a secret pc
//let return_test4 pc l x (pc':prin) l' = (c_return pc (t_return l x)) pc'

(* sanity checks for bind *)
// using a value x raises the pc 
let bind_test0 pc l x = bind (return pc l x) (fun y -> return (join pc l) l y)

// a public and trusted pc and l can be used in any computation
let bind_test1 pc l x = bind (return flow_bot flow_bot x) (fun y -> return pc l y)

// a public and trusted pc and l can be used in any computation (applied to bot context)
let bind_test2 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_bot x) (fun y -> return pc l y) flow_bot

// a public and trusted pc with any label l that flows to l' can be used in a computation with any pc' and l'
let bind_test6 l pc' (l':prin{l =<= l'}) x = bind (*flow_bot l pc' l'*) (return flow_bot l x) (fun y -> return pc' l' y) 

// negative test: flow_top doesn't (necessarily) flow to l
//let bind_test7 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_top x) (fun y -> return pc l y)
// negative test: 
//let bind_test8 pc l x = bind (*flow_bot flow_bot pc l*) (return flow_bot flow_bot x) (fun y -> return pc l y) flow_top

val apply : #a:Type -> #b:Type -> #pc:prin -> #pc':prin
            -> e:(a -> Tot (C pc' b)){pc =<= pc'}
            -> e':C pc a
            -> Tot (C pc b)
let apply (#a:Type) (#b:Type) (#pc:prin) (#pc':prin) e e' = 
  c_bind e' (fun x -> e x)

type sum (a:Type) (b:Type) =
  | L: a -> sum a b
  | R: b -> sum a b

val case : #a:Type -> #b:Type -> #c:Type -> #pc:prin -> #pc':prin
	   -> e:(C pc (sum a b)){pc =<= pc'}   
	   -> left:(a -> Tot (C pc' c))
	   -> right:(b -> Tot(C pc' c)) -> Tot(C pc c)
let case (#a:Type) (#b:Type) (#c:Type) (#pc:prin) (#pc':prin) 
	 // this didn't type-check until I added the refinement to e.  
	 //  -- why did I need it? (apply didn't require it)
	 (e:C pc (sum a b){pc =<= pc'}) (left:(a -> Tot (C pc' c))) (right:(b -> Tot(C pc' c))) =
  c_bind e (fun (x:sum a b) -> match x with | L xa -> left xa | R xb -> right xb)

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
