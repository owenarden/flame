(*--build-config 
  options:--admit_fsi FStar.Set ;
  other-files: set.fsi;
--*)
module Flame.FLAM

open FStar.Set

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

type tc_entry = (prin * prin * prin * prin)
type trust_config = set tc_entry
val add : #a:Type -> set a -> e:a -> Tot (set a)
let add s e = union s (singleton e)

assume val actsfor : trust_config -> prin -> prin -> Tot bool

assume val voice : prin -> Tot(prin)

val flowsto : trust_config -> prin -> prin -> Tot bool
let flowsto tc p q = actsfor tc (Conj (Conf q) (Integ p)) (Conj (Conf p) (Integ q))

val static_actsfor : prin -> prin -> Tot bool
let static_actsfor p q = actsfor empty p q

val flowsto_st : prin -> prin -> Tot bool
let flowsto_st p q = flowsto empty p q
  
val equiv: prin -> prin -> Tot bool
let equiv p q = static_actsfor p q && static_actsfor q p 

let flow_bot = (Integ Top)
let flow_top = (Conf Top)

assume TopPrin : forall (tc:trust_config) (p:prin) . flowsto tc p flow_top == true
assume BotPrin : forall (tc:trust_config) (p:prin) . flowsto tc flow_bot p == true
assume ReflPrin : forall (tc:trust_config) (p:prin) (q:prin). p == q ==> flowsto tc p q
assume EquivPrin : forall (tc:trust_config) (p:prin) (q:prin). equiv p q ==> flowsto tc p q
assume SymmPrin : forall (tc:trust_config) (p:prin) (q:prin). equiv p q ==> equiv q p
assume ExtPrin : forall (tc:trust_config) (tc':trust_config) (p:prin) (q:prin). 
  (subset tc tc' /\ flowsto tc p q) ==> flowsto tc' p q
assume TransPrin : forall (tc:trust_config) (p:prin) (q:prin) (r:prin) . (flowsto tc p q /\ flowsto tc q r) ==> flowsto tc p r

assume JoinIdem: forall (p:prin). {:pattern join p p} join p p == p  
assume JoinTop: forall (p:prin) . {:pattern join p flow_top} join p flow_top == flow_top 
assume JoinBot: forall (p:prin) . {:pattern join p flow_bot} join p flow_bot == p 
assume JoinComm: forall (p:prin) (q:prin). join p q == join q p
