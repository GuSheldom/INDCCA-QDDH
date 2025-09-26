(* =============================================================================
   CRYPTOGRAPHIC REDUCTION: IND-CCA1 to q-DDH
   
   This file proves the security of ElGamal encryption under the q-DDH assumption
   by constructing a reduction from any IND-CCA1 adversary to a q-DDH distinguisher.
   
   Main Components:
   1. IND-CCA1 security game definition
   2. ElGamal encryption scheme implementation  
   3. q-DDH assumption and game
   4. Reduction construction A_from_INDCCA1
   5. Vector operations and supporting lemmas
   ============================================================================= *)

(* Import required libraries for groups, lists, distributions, etc. *)
require import AllCore List DBool Group IntDiv.

theory INDCCA1_algb.

(* =============================================================================
   MATHEMATICAL SETUP: Cyclic Group and Discrete Logarithm
   ============================================================================= *)

(* Clone cyclic group theory *)
clone CyclicGroup as G.
axiom prime_p : prime G.order.  (* Group order is prime *)

(* Clone power/exponentiation module with prime order *)
clone G.PowZMod as GP with
lemma prime_order <- prime_p.

import G GP.

(* Import distribution theory for probabilistic algorithms *)
import Distr.
clone GP.FDistr as FD.
import FD.    

(* =============================================================================
   TYPE DEFINITIONS for PKE (Public Key Encryption)
   ============================================================================= *)

(** Public keys are group elements **)
type pk_t = group.

(** Secret keys are exponents **)
type sk_t = exp.

(** Plaintexts/messages (not used directly in this abstract setting) **)
(** Ciphertexts are group elements **)
type ctxt_t = group.

(** Shared/session keys for symmetric encryption **)
type key_t = group.

(** Security parameter q - number of allowed queries **)
op q : int.
axiom gt0_q : 0 < q.  (* q must be positive *)

(* =============================================================================
   PKE SCHEME INTERFACE
   ============================================================================= *)

(** Generic PKE scheme interface with key generation, encryption, decryption **)
module type Scheme = {
  proc keygen() : pk_t * sk_t           (* Generate key pair *)
  proc enc(pk : pk_t) : key_t * ctxt_t  (* Encrypt to get session key + ciphertext *)
  proc dec(c : ctxt_t, sk:sk_t) : key_t option  (* Decrypt ciphertext *)
}.

(* =============================================================================
   CCA1 ORACLES - Limited decryption oracle for CCA1 security
   ============================================================================= *)

(** Interface for oracles used in CCA1 security games **)
module type Oracles_CCA1i = {
  proc init(sk_init : sk_t) : unit                    (* Initialize with secret key *)
  proc dec(c : ctxt_t, z : exp list) : key_t option   (* Decryption with representation *)
}.

(** Core operations for group element manipulation **)
(* Product of a list of group elements *)
op prod (elements : group list) = foldr ( * ) e elements.

(* Exponentiation: compute bases[i]^exps[i] for all i, return as list *)
op ex (bases : group list)(exps : exp list) =
  (map (fun (i : group * exp) => i.`1 ^ i.`2) (zip bases exps)).

(* Product of exponentiation: compute product of ex(bases, exps) *)
op prodEx (bases : group list)(exps : exp list) =
  prod (ex bases exps).


(* Base reduction lemma: prodEx with oversized base can be truncated *)
lemma prodExBaseRed n (exps: ZModE.exp list ) f : size exps < n =>
    prodEx (map f (range 1 n)) exps  = prodEx (map f (range 1 (size exps + 1))) exps.
proof.
   rewrite /prodEx /ex. move => H.
    have p1 : size exps + 1 <= n. smt().
    have base_eq : zip (map f (range 1 n)) exps =  (zip (map f (range 1 (size exps + 1))) exps). rewrite !zip_mapl.    congr. 
    have ge0_exp : 0 <=size exps by smt(size_ge0). move : p1.
    case : (size exps + 1 = n). move =>h hi. rewrite h. smt(). move => h hi. have gt : size exps + 1 < n. smt().
    have range_split: range 1 n = range 1 (size exps + 1) ++ range (size exps + 1) n. smt(@List).  search take.
    apply (eq_from_nth (witness, witness)). have sizegt : size exps <= size (range 1 n).
    smt(@G @List).  search zip. rewrite size2_zip. smt().
    have size_eq : size (range 1 (size exps + 1 )) = size exps. rewrite size_range. simplify. smt(size_ge0).
    rewrite size2_zip. smt(). smt().
    move => i HI. search nth. rewrite nth_zip_cond.
    have HI_split : i < size (zip (range 1 n) exps) by smt(). rewrite HI_split. simplify.
    have size_eq : size (range 1 (size exps + 1 )) = size exps. rewrite size_range. simplify. smt(size_ge0). 

    rewrite (nth_zip). smt(). congr.  search nth.
    have case1 : i < size exps by smt(@G @List size_ge0 @GP). have case2 : i < n - 1 by smt(@G @List size_ge0 @GP).
    rewrite nth_range. smt(). rewrite nth_range. smt(). smt().
    rewrite base_eq. smt().
qed.


(** Limited CCA1 Oracle Implementation **)
module O_CCA1_Limited (S : Scheme)  : Oracles_CCA1i= {
  var sk : sk_t                                  (* Secret key *)
  var qs : (ctxt_t * key_t option) list         (* Query history *)
  var l : group list                            (* List of group elements seen *)

  (* Initialize oracle with secret key *)
  proc init(sk_init : sk_t) = {
    sk <- sk_init;
    qs <- [];          (* Empty query list *)
    l <- [];           (* Empty group element list *)
  }
  
  (* Decryption oracle with representation checking *)
  proc dec(c : ctxt_t, z : exp list) : key_t option = {
    var p : key_t option;
    var invalid_query : bool;

    (* Check if query is valid: 
       - Haven't exceeded q queries
       - Ciphertext matches expected representation *)
    invalid_query <- (q < size qs + 2  \/ c <> prodEx l z);

    (* Perform actual decryption using scheme *)
    p <@ S.dec(c, sk);

    (* Update state only if query was valid *)
    if (!invalid_query) {
      l <- oget p :: l ;           (* Add decrypted key to list *)
      qs <- (c, p) :: qs;      (* Record query *)
    }

    (* Return result or witness if invalid *)
    return (if !invalid_query then p else witness);
  }
}.

(* =============================================================================
   IND-CCA1 SECURITY GAME
   ============================================================================= *)

(*
  IND-CCA1 (Indistinguishability under non-adaptive Chosen-Ciphertext Attacks):
  
  1. Adversary gets public key and can make decryption queries
  2. Challenger creates challenge ciphertext with random or real session key  
  3. Adversary tries to distinguish which case occurred
  4. Adversary cannot query the challenge ciphertext
*)

(** Adversary interface for IND-CCA1 game **)
module type Adv_INDCCA1 (O : Oracles_CCA1i) = {
  proc scout(pk : pk_t) : unit {O.dec}         (* Phase 1: explore with queries *)
  proc distinguish(k : key_t, c : ctxt_t) : bool {}  (* Phase 2: distinguish challenge *)
}.

(** Key distribution for random keys **)
op dkeym (y : pk_t) = dmap FD.dt (fun (x:ZModE.exp) => (g^x)).

(** IND-CCA1 security game implementation **)
module IND_CCA1_P (S : Scheme)  (A : Adv_INDCCA1) = {
  module OS = O_CCA1_Limited(S)  (* Use limited oracle *)
  
  proc main() : bool = {
    var pk : pk_t;
    var sk : sk_t;
    var b, b' : bool;
    var k, k' : key_t;
    var c : ctxt_t;
    
    (* Generate keys *)
    (pk, sk) <@ S.keygen();
    
    (* Initialize oracle and give adversary access to pk *)
    OS.init(sk);
    OS.l <- pk :: [g];  (* Adversary has seen g and pk *)
    OS.qs <-  [];
    A(OS).scout(pk);          (* Phase 1: adversary explores *)
   
    (* Create challenge *)
    (k, c) <@ S.enc(pk);      (* Real encryption *)
    k' <$ dkeym pk;           (* Random key *)
    b <$ {0,1};               (* Random bit *)
    
    (* Challenge phase: give adversary either real or random key *)
    b' <@ A(OS).distinguish(if b then k else k', c);
    
    (* Adversary wins if they guess correctly *)
    return b' = b; 
  }
}.

end INDCCA1_algb.

(* =============================================================================
   CONCRETE INSTANTIATION: ElGamal Encryption
   ============================================================================= *)

clone include INDCCA1_algb.

import G.
import GP.
import FD.

(** ElGamal encryption scheme implementation **)
module ElGamal : Scheme = {
  (* Key generation: sk random, pk = g^sk *)
  proc keygen(): pk_t * sk_t = {
    var sk;
    sk <$ FD.dt;              (* Random secret key *)
    return (g ^ sk, sk);      (* Public key is g^sk *)
  }

  (* Encryption: return (pk^y, g^y) where y is random *)
  proc enc(pk:pk_t): key_t * ctxt_t= {
    var y;
    y <$ FD.dt;               (* Random encryption exponent *)
    return (pk ^ y, g ^ y);   (* Session key and ciphertext *)
  }
  
  (* Decryption: compute c^sk *)
  proc dec(c:ctxt_t,sk:sk_t): key_t option = {
    return Some (c ^ sk);     (* ElGamal decryption formula *)
  }
}.

(* =============================================================================
   q-DDH ASSUMPTION AND GAME
   ============================================================================= *)

(** q-DDH adversary interface **)
module type A_qDDH = {
  proc guess(gtuple : group list) : bool  (* Distinguish q-DDH tuple *)
}.

import ZModE.

(** q-DDH game: distinguish (g, g^x, g^{x^2}, ..., g^{x^q}, g^r, g^{xr}) 
    from (g, g^x, g^{x^2}, ..., g^{x^q}, g^r, g^z) where z is random **)
module QDDH (A : A_qDDH)  = {
  proc main() : bool = {
      var x, r, z , b_int;
      var gtuple : group list;
      var challenge : group;
      var b, b' : bool;

      (* Sample random values *)
      x <$ dt;   (* Secret base *)
      r <$ dt;   (* Random for challenge *)
      z <$ dt;   (* Random alternative *)

      b <$ {0,1};  (* Bit determining real or random *)
    
      (* Convert boolean to integer for computation *)
      b_int <- (if b then ZModE.zero else ZModE.one);

      (* Create q-DDH tuple: g^x, g^{x^2}, ..., g^{x^q} *)
      gtuple <- map (fun i => g^(exp x i)) (range 1 (q+1));

      (* Challenge element: either g^{xr} (real) or g^{xr+z} (random) *)
      challenge <- g^((x * r) + (z * b_int));
      
      (* Give adversary the tuple: [g^x, ..., g^{x^q}, g^r, challenge] *)
      b' <@ A.guess(gtuple ++ [g^r] ++ [challenge]);

      (* Adversary wins if they distinguish correctly *)
      return b = b';
  }
}.

(* =============================================================================
   HELPER ADVERSARIES (for testing the reduction)
   ============================================================================= *)

(** Simple adversary that converts q-DDH to IND-CCA1 for q=1  **)
module (IND_CCA1_A (A : A_qDDH) : Adv_INDCCA1) (O : Oracles_CCA1i) = {
    var pk1 : pk_t

    proc scout(pk:pk_t): unit = {
      pk1 <- pk;  (* Store public key *)
    }

    proc distinguish(k : key_t, c: ctxt_t) : bool = {
      var b;
      (* Convert IND-CCA1 challenge to q-DDH format *)
      b <@ A.guess(pk1::c::[k]);
      return b;
    }
  }.



(* =============================================================================
   VECTOR OPERATIONS for Linear Algebra over Exponents
   ============================================================================= *)

(* Zero vector of length q+1 *)
op zerov  = nseq (q+1) zero.

(* Vector addition: pointwise addition *)
op addv (a b : exp list) = map (fun (x : exp * exp) => x.`1 + x.`2) (zip a b).

(* Vector multiplication: pointwise multiplication *)
op mulv (a b : exp list) = map (fun (x : exp * exp) => x.`1 * x.`2) (zip a b).

(* Scalar multiplication: multiply vector by scalar *)
op scalev (a : exp list)(b : exp) = map (fun x => x*b) a.

(* Sum of vectors: fold addition over list of vectors *)
op sumv (a : exp list list) = foldr addv zerov a.


op shift_trunc (v : exp list) = take (q+1) (zero :: v).

(* =============================================================================
   MAIN REDUCTION: IND-CCA1 to q-DDH
   
   This is the heart of the security proof. We construct a q-DDH adversary
   that uses an IND-CCA1 adversary as a subroutine.
   ============================================================================= *)


(* =============================================================================
   SUPPORTING LEMMAS for the Security Proof
   ============================================================================= *)

section Security.


(* Basic list operation lemmas *)
lemma zip_cons (x : 'a) (y : 'b) (xs : 'a list) (ys : 'b list) :
    zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys.
    proof. smt(). qed.

lemma prod_cons (x : group) (xs : group list) :
     prod (x :: xs) = x * prod xs. 
     proof. smt(). qed.

lemma map_cons (f : 'a -> 'b) (x : 'a) (xs : 'a list) :
       map f (x :: xs) = f x :: map f xs. 
       proof. smt(). qed.

lemma map_nil (f : 'a -> 'b): map f [] = []. 
      proof. smt(). qed.

(* Map constant function gives nseq *)
lemma map_const ['a 'b] (c : 'b) (xs : 'a list):
  map (fun (_ : 'a) => c) xs = nseq (size xs) c.
proof.
elim: xs => [|x xs IH].
- rewrite map_nil nseq0 //.
- rewrite map_cons IH -nseqS.
  + rewrite size_ge0 //.
  trivial. smt().
qed.




(* Product of empty list is identity *)
lemma prod_nil : prod [] = e.
    proof. by []. qed.
  
(* Product of n copies of g equals g^n *)
lemma prod_nseq (n : int) (g : group) :
  0 <= n => prod (nseq n g) = g ^ n.
proof.
elim/natind: n => [n le0_n|n ge0_n IH].
- (* Base case: n <= 0 *)
  rewrite nseq0_le // prod_nil.
  move => h. have n_eq_zero: n = 0. smt(). rewrite n_eq_zero. 
  rewrite exp0. smt().
  
- (* Inductive case: n -> n+1 *)
  rewrite nseqS // prod_cons IH. smt(). 
  move=> ge0_n1. rewrite expS //. rewrite mulcC. smt().
qed.

(* Product of n identity elements is identity *)
lemma prod_nseq_unit (n : int) :
  0 <= n => prod (nseq n e) = e.
proof.
   move=> ge0_n.
   rewrite prod_nseq //. 
   rewrite expc1. smt().
qed.





(* Zip with empty list gives empty result *)
lemma zip_nil_l ['a 'b] (l : 'b list) : zip<:'a,'b> [] l = [].
proof. by case: l. qed.

lemma zip_nil_r ['a 'b] (l : 'a list) : zip<:'a,'b> l [] = [].
proof. by case: l. qed.

(* =============================================================================
   KEY LEMMAS for Group Operations and Exponentiation
   ============================================================================= *)

(* Distributivity: (prod gs)^n = prod (map (^n) gs) *)
lemma prod_exp_distributive (gs : group list) (n : exp) :
  prod gs ^ n = prod (map (fun g => g ^ n) gs).
proof.
  elim: gs => [|g gs IH] //=. 
  smt(@G @GP @List). 
  rewrite /= !prod_cons. 
  have exp_mult_dist: (g * prod gs) ^ n = g ^ n * (prod gs) ^ n. 
    smt(@G @GP).
  rewrite exp_mult_dist. rewrite IH. smt().
qed.




(* =============================================================================
   PRODEX SCALING AND MANIPULATION LEMMAS
   
   These lemmas show how to manipulate prodEx expressions, which is essential
   for the oracle simulation. They establish that we can "factor out" exponents
   and rearrange computations while preserving equality.
    ============================================================================= *)


(* Scaling lemma: prodEx with scaled exponents *)
lemma prodExScale1 bases exp scala :
    prodEx bases exp ^ scala = prodEx bases (scalev exp scala).
proof.
  rewrite /prodEx. rewrite /ex. rewrite !prod_exp_distributive. congr. 
  rewrite /scalev. search zip. rewrite zip_mapr. 
  rewrite -!map_comp. congr. apply fun_ext => xy.
  by case: xy => [x y] /=; rewrite /(\o) /= expM.
qed.

(* Alternative scaling lemma using ex *)
lemma prodExScale2 bases exp scale :
    prodEx bases exp ^ scale = prodEx (ex bases (nseq (size bases) scale)) exp.
proof.
  rewrite prodExScale1. rewrite !/prodEx /ex. congr.
  elim: bases exp => [|base_h base_t IH] [|exp_h exp_t] //=.
  rewrite !zip_nil_l. smt(). 
  rewrite !zip_nil_l. smt(). 
  rewrite zip_nil_r. rewrite /scalev. rewrite zip_nil_r. smt(). 
  rewrite /scalev /=. simplify.
  have nseq_cons: nseq (1 + size base_t) scale = scale :: nseq (size base_t) scale. 
    rewrite -nseqS. smt(size_ge0). smt(@G). 
  rewrite nseq_cons. simplify.
  split. smt(@G @GP). rewrite IH. smt().
qed.

(* Cons with zero exponent lemma *)
lemma prodExCons bs e b :
  prodEx (b :: bs) (zero :: e) = prodEx bs e.
proof.
  rewrite /prodEx /ex. rewrite zip_cons. rewrite map_cons. rewrite prod_cons. 
  rewrite /= exp0. smt(@G @GP @List).
qed.

(* General cons lemma for prodEx *)
lemma prodExConsGeneral (g : group) (gs : group list) (e : exp) (es : exp list) :
  prodEx (g :: gs) (e :: es) = g ^ e * prodEx gs es.
proof.
  rewrite /prodEx /ex.
  rewrite zip_cons map_cons prod_cons.
  trivial.
qed.

(* Triple zip associativity *)
lemma map_zip3_assoc ['a 'b 'c 'd] 
  (f : 'a -> 'b -> 'c -> 'd)
  (l1 : 'a list) (l2 : 'b list) (l3 : 'c list) :
  map (fun xy_z => let (xy, z) = xy_z in 
                   let (x, y) = xy in 
                   f x y z)
      (zip (zip l1 l2) l3) =
  map (fun x_yz => let (x, yz) = x_yz in 
                   let (y, z) = yz in 
                   f x y z)
      (zip l1 (zip l2 l3)).
proof.
  elim: l1 l2 l3 => [|x1 xs1 IH] l2 l3 //=.
  by rewrite !zip_nil_l !map_nil.
  case: l2 => [|x2 xs2]. 
    rewrite !zip_nil_r !zip_nil_l. rewrite !map_nil. smt().
  case: l3 => [|x3 xs3]. 
    rewrite !zip_nil_r. rewrite !map_nil. smt(). 
  rewrite !/zip /=. apply IH.
qed.

(* Double prodEx composition *)
lemma prodExEx b e1 e2 :
    prodEx (ex b e1) e2 = prodEx b (mulv e1 e2).
proof.
  rewrite /prodEx /ex /mulv. rewrite zip_mapl. rewrite zip_mapr. 
  rewrite -!map_comp. congr. rewrite /(\o) /=.
  elim: b e1 e2 => [|g_h g_t IH] [|e1_h e1_t] [|e2_h e2_t] //=.
  split. smt(@G @GP). by apply IH.
qed.







(* Ex with map and constant scaling *)
lemma ex_map_prodEx bases exps size_bases size_exps c :
    size_bases = size bases => size_exps = size exps =>
    ex (map (prodEx bases) exps) (nseq size_exps c) = 
    map (prodEx (ex bases (nseq size_bases c))) (exps).
proof. 
  move => h h0. apply (eq_from_nth g). smt(@List). 
  move => i hi. rewrite /ex.
  rewrite (nth_map (witness, witness) g). smt(@List size_ge0). 
  rewrite nth_zip. smt(size_ge0 @List). simplify. 
  rewrite (nth_map witness). smt(size_ge0 @List).
  rewrite nth_nseq. smt(size_ge0 @List).

  have inner_ex: 
    map (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) (zip bases (nseq size_bases c)) = 
      ex bases (nseq size_bases c). 
    rewrite /ex //. 
  rewrite inner_ex. 
  rewrite (nth_map (witness ) g). smt(size_ge0 @List). 
  rewrite h.
  rewrite -prodExScale2. smt().
qed.
  
(* Map exponentiation with range *)
lemma prodExMap g (x : exp) (s e : int) :
    map (fun i => g ^ exp x i) (range s e) = 
    ex (nseq (e-s) g) (map (fun i => exp x i) (range s e)).
proof.
  apply (eq_from_nth g). smt(@List). 
  move => i hi. rewrite (nth_map 0). smt(@List).
  move => @/ex. rewrite (nth_map (g,zero)). smt(@List). 
  simplify. smt(@List).
qed.



(** ADDITION DISTRIBUTIVITY LEMMA
    This is one of the most important lemma for the oracle simulation.
    It shows that: prodEx(bases, a + b) = prodEx(bases, a) * prodEx(bases, b)
    
    This means that adding representation vectors corresponds to multiplying
    the corresponding group elements, which is exactly what we need for
    simulating linear combinations in the oracle. **)

(* Addition distributivity for prodEx *)
lemma prod_ex_addv (base : group list) (a b : exp list) :
    size a = size base => size b = size base =>
    prod (ex base (addv a b)) = prod (ex base a) * prod (ex base b).
proof.
  move=> size_a size_b.
  rewrite /addv.
  move: a b size_a size_b.
  elim: base.
  move=> a b size_a size_b. rewrite /ex. rewrite !zip_nil_l.
    by smt(@List @G). 
  move=> g gs IH a b size_a size_b.
  case: a size_a => [|a_h a_t] size_a; first by smt(@List).
  case: b size_b => [|b_h b_t] size_b; first by smt(@List). 
  rewrite /ex !zip_cons !map_cons !prod_cons /=. 
  rewrite prod_cons expD /ex. rewrite IH. smt(@G @GP). smt(). rewrite /ex. 

  pose A := prod (map (fun (i : group * GP.exp) => i.`1 ^ i.`2) (zip gs a_t)).
  pose B := prod (map (fun (i : group * GP.exp) => i.`1 ^ i.`2) (zip gs b_t)).
  pose X := g ^ a_h.
  pose Y := g ^ b_h. 
  rewrite mulcA. rewrite mulcA. congr.

  have com : Y * A = A * Y. rewrite mulcC. smt(). 
  rewrite -mulcA. rewrite com. 
  smt(@G @GP). 
qed.



(* sumv concat lemma*)
lemma sumv_cons (v : exp list) (vs : exp list list) :
    sumv (v :: vs) = addv v (sumv vs).
proof.
  rewrite /sumv. simplify. smt(). 
qed.


(* ProdEx with empty exponent list is identity *)
lemma prodEx_nil_r (bases : group list) :
  prodEx bases [] = e.
proof.
  rewrite /prodEx /ex.
  rewrite zip_nil_r.
  rewrite map_nil.
  rewrite prod_nil.
  trivial.
qed.

lemma prodEx_nil_l (exps : exp list) :
  prodEx [] exps = e.
proof.
  rewrite /prodEx /ex.
  rewrite zip_nil_l.
  rewrite map_nil.
  rewrite prod_nil.
  trivial.
qed.

lemma prodEx_nil :
  prodEx [] [] = e.
proof.
  by rewrite prodEx_nil_l. 
qed.

(* Vector addition with empty left operand *)

lemma addv_nil_l (b : exp list) :
  addv [] b = [].
proof.
  rewrite /addv.
  rewrite zip_nil_l.
  rewrite map_nil.
  trivial.
qed.

(* Vector addition with empty right  operand *)

lemma addv_nil_r (a : exp list) :
  addv a [] = [].
proof.
  rewrite /addv.
  rewrite zip_nil_r.
  rewrite map_nil.
  trivial.
qed.

(* Vector addition with empty  operand *)

lemma addv_empty (a b : exp list) :
  a = [] \/ b = [] =>
  addv a b = [].
proof.
  case => [a_empty | b_empty].
  - by rewrite a_empty addv_nil_l.
  - by rewrite b_empty addv_nil_r.
qed.


(* Sum of empty vector list is zero vector *)
lemma sumv_nil :
  sumv [] = zerov.
proof.
  by rewrite /sumv. 
qed.


(* Behead is equivalent to drop 1 *)
lemma behead_drop (bases: group list) :
    behead bases = drop 1 bases.
proof.
    smt(@List).
qed.






(* ProdEx with oversized exponent list can be truncated *)
lemma prodEx_sizele a b :
    size a < size b => prodEx a b = prodEx a (take (size a) b).
proof.
    move => size_neq.
    rewrite /prodEx /ex.
    congr.  congr.
    elim: a b size_neq => [|a_h a_t IH] [|b_h b_t] //= size_lt.
    have h : !( 1 + size a_t <= 0) by smt(size_ge0). rewrite h. simplify. rewrite IH. smt(). smt().
qed.
    





(* Shift-truncate lemma: key property for oracle simulation
    This lemma shows that when the last element of exps is zero,
    applying shift_trunc and using the full base is equivalent to
    using the tail of the base with the original exponents.
    
    Intuitively: prodEx([g, g^x, g^{x^2}, ...], shift_trunc([a, b, c, ..., 0])) 
                = prodEx([g^x, g^{x^2}, ...], [a, b, c, ..., 0])
    
    This is crucial for the reduction's oracle simulation where we need to
    maintain consistency between different representations. *)

lemma prodExShiftTrunce bases exps:
       size bases = q +1  =>
       size exps = q + 1 =>
       drop q exps = nseq 1 zero =>
       prodEx bases (shift_trunc exps) = prodEx (behead bases) exps.
proof.
      move=>  size_bases size_exps last_zero.
      rewrite /shift_trunc.
      have take_eq : (take (q+1) (zero :: exps)) = zero :: (take q exps).
      smt(@List gt0_q).
      rewrite take_eq.
      have exps_split: exps = take q exps ++ [zero].  rewrite -(cat_take_drop q).
      have h : take q (take q exps ++ drop q exps) = take q exps. search take.
      have size_take_q : size(take q exps) = q by smt(@List gt0_q). 
      rewrite take_size_cat. smt(). smt(). rewrite h. rewrite last_zero. smt(@List @G @GP).
      rewrite exps_split.
      have size_take_q : size(take q exps) = q by smt(@List gt0_q). 
      rewrite take_size_cat. smt().
      have base_cons : (head witness bases) :: (behead bases) =bases.
      have : bases <> []. smt(). 
      apply head_behead. 
      have h : (prodEx bases (zero :: take q exps)) =
      prodEx (head witness bases :: behead bases) (zero :: take q exps). smt().
      rewrite h.
      rewrite prodExCons.
      pose oversize := (take q exps ++ [zero]).
      pose a := (behead bases).  
      rewrite (prodEx_sizele a oversize). smt().  have size_a:  size a = q by smt(@G @List @GP gt0_q).
      rewrite size_a.   rewrite /oversize. 
      rewrite take_size_cat. smt(@List @G gt0_q). smt().
qed.




(* Size of sum of vectors with uniform size *)
lemma size_sumv (l : exp list list) :
  (forall v, v \in l => size v = q + 1) =>
  size (sumv l) = q + 1.
  proof.
  
    elim: l => [|v vs IH]. move => H.
    rewrite sumv_nil /zerov size_nseq.
    smt(gt0_q). 
    move => H.
    rewrite sumv_cons.
    have Hv: size v = q + 1.
    apply H. by rewrite in_cons. 
    have Hrec: size (sumv vs) = q + 1.
    apply IH.  move=> u Hu. apply H. by rewrite in_cons Hu orbT.
    rewrite /addv size_map size_zip Hv Hrec.
    smt(@G @GP).
qed.

(* ProdEx distributes over vector addition *)
lemma prodEx_addv_distributive (bases : group list) (a b : exp list) :
   size a = size bases => size b = size bases =>
   prodEx bases (addv a b) = prodEx bases a * prodEx bases b.
proof.
    move => ha hb.
    rewrite /prodEx prod_ex_addv. smt(). smt(). smt().
qed.

(* ProdEx with all zero exponents is identity *)
lemma prodEx_nseq_zero (bases : group list) (n : int) :
  0 <= n =>
  prodEx bases (nseq n zero) = e.
proof.
  move=> ge0_n.
  rewrite /prodEx /ex.
  elim: bases n ge0_n => [|g gs IH] n ge0_n.
  - (* bases = [] *)
    by rewrite zip_nil_l map_nil prod_nil.
  - (* bases = g :: gs *)
    case: (n = 0) => [n_zero | n_pos].
    + (* n = 0 *)
      rewrite n_zero nseq0.
      by rewrite zip_nil_r map_nil prod_nil.
    + (* n > 0 *)
  have n_gt0: 0 < n by smt().
  have nseq_cons: nseq n zero = zero :: nseq (n-1) zero.  search nseq. rewrite -nseqS. smt(). simplify. trivial.
  rewrite nseq_cons zip_cons map_cons prod_cons /= exp0 IH. 
  smt(). smt(@G @GP).
qed.



  


(* Simplification: prepending g to powers equals mapping from 0 *)
lemma q0_simp (sk : exp) :
      (g :: map (fun (i : int) => g ^ exp sk (i))(range 1 (q+1 ))) =
      map (fun (i : int) => g ^ exp sk (i))(range 0 (q + 1 )).
 proof. 
  have range_split: range 0 (q + 1) = 0 :: range 1 (q + 1).
  smt(@ G @GP @List gt0_q). rewrite range_split map_cons.
  congr. smt(@G @GP).
qed.

(* Size of scaled vector equals original size *)
lemma size_scalev (v : exp list) (s : exp) :
  size (scalev v s) = size v.
proof.
  by rewrite /scalev size_map.
qed.

(* Ex operation distributes over cons structure *)
lemma ex_cons_general:
  forall (x : group) (xs : group list) (e : ZModE.exp) (es : ZModE.exp list),
  ex (x :: xs) (e :: es) = (x ^ e) :: ex xs es.
proof.
  move => x xs e es .
  rewrite /ex /=. trivial.
qed.

(* Ex with range shift property *)
lemma ex_range_shift (sk : exp) :
  ex (map (fun (i : int) => g ^ exp sk i) (range 0 (q + 1))) (nseq (q + 1) sk) =
  map (fun (i : int) => g ^ exp sk i) (range 1 (q + 2)).
    
proof.
  rewrite /ex.
  have Hlen: size (range 0 (q + 1)) = size (nseq (q + 1) sk) by rewrite size_range size_nseq.
  rewrite zip_mapl -map_comp /(\o). 
  apply (eq_from_nth witness). 
  rewrite size_map size_zip size_range size_nseq.
  smt(@List @G @GP).
  move=> i hi.
  rewrite !(nth_map witness) //. smt(@List). smt(@List @G @GP).
  case (0 <= i < q + 1) => [valid_i|]; last smt(@List).
  simplify.
  have zip_nth: nth witness (zip (range 0 (q + 1)) (nseq (q + 1) sk)) i = (i, sk).
  have range_i: nth witness (range 0 (q + 1)) i = i.
  rewrite nth_range //.
  have nseq_i: nth witness (nseq (q + 1) sk) i = sk.
  rewrite nth_nseq_if valid_i. smt().
  (* Zip structure property: nth element of zip equals pair of nth elements *)
  have zip_structure: forall j, 0 <= j < min (size (range 0 (q + 1))) (size (nseq (q + 1) sk)) =>
  nth witness (zip (range 0 (q + 1)) (nseq (q + 1) sk)) j = 
  (nth witness (range 0 (q + 1)) j, nth witness (nseq (q + 1) sk) j).
  move=> j hj. smt(@List).
  rewrite zip_structure. smt(@List @G @GP).
  rewrite range_i nseq_i. smt().
  rewrite zip_nth. rewrite /= nth_range //. 
  simplify. rewrite -expM. congr.
  smt(@G @GP @ZModE).
qed.



(* Drop from nseq of zeros simplify *)
lemma drop_nseq_zero (n k : int) :
     0 <= n <= k =>
     drop n (nseq k zero) = nseq (k - n) zero.
proof.
  move=> bounds.
  apply (eq_from_nth witness).
  rewrite size_drop. smt().  rewrite size_nseq.
  smt(@GP @List @G gt0_q).
  move=> i hi.
  rewrite nth_drop. smt(). smt(). rewrite  nth_nseq.
  move: hi.
  rewrite size_drop. smt().
  rewrite size_nseq.  smt().  rewrite nth_nseq. move: hi.
  rewrite size_drop. smt().
  rewrite size_nseq. smt(). trivial. 
qed.

(* Drop from nseq general case *)
lemma drop_nseq (n k : int) (x : 'a ):
  0 <= n <= k =>
  drop n (nseq k x) = nseq (k - n) x.
proof.
  move=> bounds.
  apply (eq_from_nth witness).
  rewrite size_drop. smt().  rewrite size_nseq.
  smt(@GP @List @G gt0_q).
  move=> i hi.
  rewrite nth_drop. smt(). smt(). rewrite  nth_nseq.
  move: hi.
  rewrite size_drop. smt().
  rewrite size_nseq.  smt().  rewrite nth_nseq. move: hi.
  rewrite size_drop. smt().
  rewrite size_nseq. smt(). trivial. 
qed.


(** Take from nseq **)
lemma take_nseq (n k : int) (x : 'a ):
    0 <= n <= k =>
    take (k - n) (nseq k x) = nseq (k - n) x.
proof.
 move=> [ge0_n le_nk].
 apply (eq_from_nth witness).
 rewrite size_take. smt().  rewrite !size_nseq.
 rewrite !StdOrder.IntOrder.ler_maxr. smt(). smt(). smt().
 rewrite size_take. smt().
 move=> i hi.
 rewrite nth_take. smt().
 smt(). rewrite nth_nseq.
 move: hi. smt().
 rewrite nth_nseq. move: hi. rewrite !size_nseq.
 smt().
 trivial. 
qed.

(* Drop commutes with scalev *)
lemma drop_scalev (v : exp list) (s : exp) (n : int) :
  drop n (scalev v s) = scalev (drop n v) s.
proof.
  rewrite /scalev.
  by rewrite map_drop.
qed.



(* Map over nseq *)
lemma map_nseq (f : 'a -> 'b) (n : int) (x : 'a) :
  map f (nseq n x) = nseq n (f x).
proof.
  elim/natind: n => [n le0_n|n ge0_n IH].
  - rewrite nseq0_le // map_nil nseq0_le //.
  - rewrite nseqS // map_cons IH nseqS //.
qed.



(** Scalev of nseq **)
lemma scalev_nseq (n : int) (x c : ZModE.exp) :
  scalev (nseq n x) c = nseq n (x * c).
proof.
  rewrite /scalev.
  by rewrite map_nseq.
qed.

(* Scalev of nseq 0 *)
lemma scalev_nseq_zero (n : int) (c : ZModE.exp) :
  scalev (nseq n zero) c = nseq n zero.
proof.
  rewrite scalev_nseq. smt(@ZModE).
qed.

(** Drop commutes with addv **)
lemma drop_addv (n : int) (u v : ZModE.exp list) :
  size u = size v => drop n (addv u v) = addv (drop n u) (drop n v).
    proof.
    move => size_eq.
    elim: u v n size_eq => [|u_head u_tail IH] [|v_head v_tail] n //=. smt(). smt().
    move=> size_eq.
    case: (n <= 0) => [le0_n|/ltzNge gt0_n]. smt(). smt().
qed.



(* Addv with size inequality a <= b*)
lemma addv_neq a b :
    size a <= size b => addv a b = addv a (take (size a) b).
    proof.
    move=> size_lt.
    rewrite /addv. 
    congr. elim: a b size_lt => [|x xs IH] [|y ys] //= size_lt. smt().
qed.
   

(** Drop and take equivalence for nseq: dropping n elements equals taking the remaining k-n elements **)
lemma drop_nseq_eq_take (n k : int) (x : 'a) :
  0 <= n <= k =>
  drop n (nseq k x) = take (k - n) (nseq k x).
proof.
  move=> [ge0_n le_nk].
  rewrite drop_nseq. smt().
  rewrite take_nseq. smt(). trivial.
qed.









(* Drop commutes with sumv: dropping elements from sum equals sum of dropped elements
    This is a key lemma for vector operations in the reduction, showing that
    drop and sumv operations can be interchanged under certain conditions. *)
lemma drop_sumv (n : int) (xs : ZModE.exp list list) :
  xs <> [] =>                              (* xs is non-empty *)
  all (fun v => size v = q + 1) xs =>     (* all vectors have uniform size q+1 *)
  0 <= n <= q =>                          (* drop index is valid *)
  drop n (sumv xs) = sumv (map (drop n) xs).
proof.
  move=>  xs_nonempty all_size_eq [ge0_n len_q].
  (* Establish that xs has at least one element *)
  have  xs_largeT : 1 <= size xs by smt(@List).
  move : xs_largeT.
  (* Induction on the list xs *)
  elim: xs xs_nonempty all_size_eq => [|v vs IH] xs_nonempty all_size.
  - (* Base case: xs = [] - contradiction with non-empty assumption *)
    by []. 
  (* Inductive case: xs = v :: vs *)
  have v_size: size v = q + 1 by smt(@List ).                    (* v has size q+1 *)
  have vs_all_size: all (fun u => size u = q + 1) vs by smt(@List). (* vs elements have size q+1 *)
  
  (* Rewrite using sumv_cons and map_cons *)
  rewrite sumv_cons map_cons sumv_cons.
  (* Key step: drop commutes with addv since both operands have same size *)
  rewrite drop_addv. rewrite size_sumv.  smt(@List @ZModE ). smt().
  move=> size_ge1.
  have : 0<= size vs.  smt(@List). move => size_ge0.
  (* Case analysis on whether vs is empty or not
     Case 1 : vs has at leat 1 elements *)
  case: (1 <=size vs ) => [vs_ge1|vs_eq0]. rewrite IH.
  smt(). smt(). smt(). trivial.
  (* Case 2: vs is empty *)
  have vs_empty : vs = [] by smt(@List). rewrite vs_empty map_nil.
  (* When vs is empty, sumv vs = zerov *)
  rewrite sumv_nil.  rewrite /zerov.
  (* Use addv_neq to handle size mismatch between drop n v and zerov *)
  rewrite (addv_neq (drop n v) (nseq (q + 1) zero)).
  rewrite size_drop. smt(). rewrite v_size size_nseq. have rev : 0 < q + 1 -n  by smt().
  rewrite !StdOrder.IntOrder.ler_maxr. smt(). smt().  smt().
  (* Establish size equality for the final step *)
  have : size (drop n v) = q + 1 -n. rewrite size_drop. smt(). rewrite v_size. smt(@GP @G).
  move => size_dd. rewrite size_dd.  congr. 
  (* Final simplification using drop_nseq_eq_take *)
  rewrite drop_nseq_eq_take. smt(). trivial.
qed.






(** Sum of n copies of zero vector equals zero vector
    This lemma establishes that summing any number of zero vectors gives the zero vector,
    which is fundamental for vector arithmetic in the reduction. **)

lemma sumv_nseq_zerov (n : int) : 
     0 <= n =>
     sumv (nseq n zerov) = zerov.
proof.
         elim/natind: n => [n le0_n|n ge0_n IH].
  - (* Base case: n <= 0 *)
    move=> _.
    (* When n <= 0, nseq gives empty list, sumv of empty list is zerov *)
     rewrite nseq0_le // sumv_nil //.

    (* Inductive case: n >= 0 *)
    move=> ge0_n1.
    rewrite nseqS // sumv_cons. rewrite IH //.
    have addv_zero_identity: addv zerov zerov = zerov.
    rewrite /addv /zerov.
    (* Prove equality by showing each element is equal *)
    apply (eq_from_nth zero).
  - rewrite !size_map !size_zip !size_nseq. smt().
  - move=> i hi.
    rewrite size_map size_zip !size_nseq in hi.
    have hi_simplified: 0 <= i < q + 1. smt(). rewrite (nth_map (zero, zero)) //.
    rewrite size_zip !size_nseq. smt().
    (* Each element of zip is (zero, zero), and zero + zero = zero *)
    rewrite nth_zip //.  rewrite /=.
    rewrite !nth_nseq_if. simplify. smt(@GP @ZModE @G).
    (* Apply the zero identity to complete the proof *)
    rewrite addv_zero_identity. smt().
qed.




(** Sum of n singleton zero vectors equals one singleton zero vector
    This lemma shows that summing any positive number of singleton zero vectors
    [nseq 1 zero] results in a single singleton zero vector. This is important
    for handling uniform-sized vector operations in the reduction. **)
lemma sumv_nseq_zero_singleton (n : int) :
     1 <= n =>
     sumv (nseq n (nseq 1 zero)) = nseq 1 zero.
proof.
  move=> ge1_n.
  (* Induction on n *)
  elim/natind: n ge1_n => [m le0_m|m ge0_m IH] ge1_n.
  - (* Base case: m <= 0 *)
    (* Contradiction: we have 1 <= n and n = m, but m <= 0 *)   
    smt().
    
  - (* Inductive case: m >= 0 *)
  case: (m = 0) => [m_eq_0|m_neq_0].

  + (* Case m = 0, so n = 1 *)
  rewrite m_eq_0. rewrite nseqS. smt().  rewrite nseq0. rewrite sumv_cons sumv_nil. rewrite /addv.
  rewrite /zerov.  have : (zip (nseq 1 zero) (nseq (q + 1) zero)) =   (zip (nseq 1 zero) (nseq (1) zero)).
  rewrite nseqS. smt(gt0_q).  rewrite nseq1.   rewrite zip_cons. rewrite zip_nil_l. smt().

  move =>H. rewrite H. apply (eq_from_nth zero). rewrite size_map size_zip !size_nseq.
  (* left：size (map ... (zip ...)) = size (zip ...) = min 1 1 = 1 *)
  (* right：size (nseq 1 zero) = 1 *)
  smt(). move=> i hi.
  rewrite size_map size_zip !size_nseq in hi.
  (* hi: 0 <= i < 1, i = 0 *)
  have i_eq_0: i = 0 by smt().
  rewrite i_eq_0.  rewrite (nth_map (zero, zero)) //.
  + (* prove index valid *)
  rewrite size_zip !size_nseq. smt(). rewrite !nth_zip //.
  rewrite /= !nth_nseq_if /=. 
  smt(@ZModE). have ge1_m: 1 <= m by smt(). rewrite nseqS //.



  rewrite sumv_cons. rewrite IH. smt(). rewrite /addv.
  apply (eq_from_nth zero).
  rewrite !size_map !size_zip !size_nseq.
  smt().
  move=> i hi.
  rewrite size_map size_zip !size_nseq in hi.
  have i_eq_0: i = 0 by smt().
  rewrite i_eq_0.
  rewrite (nth_map (zero, zero)) //.
  + rewrite size_zip !size_nseq. smt().
  
  rewrite nth_zip //. rewrite /= !nth_nseq_if /=.
  smt(@ZModE).
qed.


lemma zip_cat_distributive (a1 a2 : 'a list) (b1 b2 : 'b list) :
  size a1 = size b1 =>
  zip (a1 ++ a2) (b1 ++ b2) = zip a1 b1 ++ zip a2 b2.
proof.
  move=> size_eq.
  apply (eq_from_nth witness).
  
  - (* size equal *)
  rewrite size_zip size_cat.  smt(@G @GP @List).
  - (* equal each element *)
    move=> i hi.
    rewrite size_zip size_cat in hi.
    
    (* dicuss the locate of i *)
    case: (i < size a1) => [i_lt_a1|i_ge_a1]. rewrite nth_cat.
  - smt(@List). smt(@List).

qed.



lemma prod_cat (xs ys : group list) :
  prod (xs ++ ys) = prod xs * prod ys.
proof.
  elim: xs => [|x xs IH].
  - (* Base case: xs = [] *)
    rewrite cat0s.
    (* prod ([] ++ ys) = prod ys *)
    (* prod [] * prod ys = 1 * prod ys = prod ys *)
    rewrite prod_nil.
    smt(@G @GP).
  - (* Inductive case: xs = x :: xs *)
    rewrite cat_cons.
    (* prod ((x :: xs) ++ ys) = prod (x :: (xs ++ ys)) *)
    rewrite prod_cons.
    (* = x * prod (xs ++ ys) *)
    rewrite IH.
    (* = x * (prod xs * prod ys) *)
    rewrite prod_cons.
    (* prod (x :: xs) * prod ys = (x * prod xs) * prod ys *)
    algebra. 
qed.


(** Product split with last zero exponent
    This lemma shows that when the last exponent in a list is zero, the product
    can be computed by ignoring the last base-exponent pair. This is crucial for
    oracle simulation where we need to handle cases with trailing zero exponents.
    
    Intuitively: prodEx([g1, g2, ..., gn], [a1, a2, ..., an-1, 0]) 
                = prodEx([g1, g2, ..., gn-1], [a1, a2, ..., an-1])
    
    This property allows the reduction to efficiently handle representations
    that have zero coefficients in the last position. **)
lemma prodEx_split_last_zero (bases : group list) (exps : ZModE.exp list) :
  size bases = size exps =>
  0 <size exps  =>
  nth witness exps (size exps - 1) = zero =>
  prodEx bases exps = 
  prodEx (take (size bases - 1) bases) (take (size exps - 1) exps).
proof.
  move=> size_eq size_gt0 last_zero.
  
  (* split exps into prefix and last element*)
  have exps_split: exps = take (size exps - 1) exps ++ [zero].
  rewrite -(cat_take_drop (size exps - 1)).
  have drop_last: drop (size exps - 1) exps = [nth witness exps (size exps - 1)]. smt( @List). smt(@List). 
 
  
  (* split bases into prefix and last element *)
  have bases_split: bases = take (size bases - 1) bases ++ [nth witness bases (size bases - 1)].
  rewrite -(cat_take_drop (size bases - 1)).
  have drop_last_base: drop (size bases - 1) bases = [nth witness bases (size bases - 1)]. smt(@List). smt(@List).
  have tran : prodEx bases exps = prodEx (take (size bases - 1) bases ++
             [nth witness bases (size bases - 1)]) (take (size exps - 1) exps ++ [zero]). smt(). rewrite tran.
  rewrite /prodEx /ex. rewrite -bases_split.
            (* split zip and map *)
  have zip_split: zip bases (take (size exps - 1) exps ++ [zero]) = 
               zip (take (size bases - 1) bases) (take (size exps - 1) exps)
               ++ zip (drop (size bases - 1) bases) [zero].
           
  rewrite -zip_cat_distributive. rewrite !size_take.

  smt(). smt(). simplify. smt(). smt(@List). rewrite zip_split.  rewrite map_cat. rewrite prod_cat.
  have : prod (map (fun (i : group * GP.exp) => i.`1 ^ i.`2)
              (zip (drop (size bases - 1) bases) [zero])) = e.
  have drop_single: drop (size bases - 1) bases = [nth witness bases (size bases - 1)].
  smt(@List). rewrite drop_single.
  simplify. search exp.

  have exp_zero: (nth witness bases (size bases - 1)) ^ zero = e. smt(@G @GP).
  rewrite exp_zero. smt(@G @GP). smt(@G @GP).

qed.
    

(* my version of relation between behead and drop*)
lemma my_behead_drop (base : group list) : behead base = drop 1 base.
    case: base => [|x xs].
  - (* base = [] *)
    rewrite behead_nil -drop0.
    by [].
  - (* base = x :: xs *)
    rewrite behead_cons drop_cons. simplify.
    smt(@G @GP @List).
qed.


(* distributive of nth and addv*)
lemma addv_nth (a b : ZModE.exp list) (pos : int) :
  size a = size b =>
  0 <= pos < size a =>
  nth witness (addv a b) pos = nth witness a pos + nth witness b pos.
proof.
  move=> size_eq pos_valid.
  rewrite /addv. rewrite(nth_map witness witness). smt(@List). smt( @List).
qed.



  
module (A_from_INDCCA1 (A : Adv_INDCCA1) : A_qDDH) = {
  
  (* State variables for the reduction *)
  var gxs : group list        (* Powers g^x, g^{x^2}, ..., g^{x^q} *)
  var l : group list          (* List of group elements (oracle state) *)
  var reps : exp list list    (* Linear representations of l in basis (g::gxs) *)
  
  (* Internal oracle that simulates CCA1 oracle using q-DDH challenge *)
  module O_Internal : Oracles_CCA1i = {
    var sk : sk_t
    var qs : (ctxt_t * key_t option) list
    var challenge_c : ctxt_t 

    proc init(sk_init : sk_t) = {
    sk <- sk_init;
       qs <- [];
      
      l <- [];
    }

    (* Core oracle: simulate decryption without knowing secret key *)
    proc dec(c : ctxt_t, z : exp list) : key_t option = {
      var p : key_t option;
      var rep_c, rep_p;
      var invalid_query : bool;

      (* Validity check: query limit and representation consistency *)
      invalid_query <- (q < size qs + 2  \/ c <> prodEx l z);

      (* Compute representation of ciphertext in basis (g::gxs) *)
      rep_c <- sumv (map (fun x : exp list * exp => scalev x.`1 x.`2)
         (zip reps z)); 
           (* Prepend zero for g^0 term *)
       rep_p <- ( shift_trunc rep_c); 
      
      (* Compute corresponding group element *)
      p <- Some (prodEx (g :: gxs) (rep_p));
      
      (* Update state if query was valid *)
           if (!invalid_query) {
        reps <- rep_p :: reps ;
        l <-   oget p :: l ;           (* Add to group element list *)
        qs <- (c, p) :: qs;      (* Record query *)
             (* Store representation *)
      }
     
      (* Return result *)
      return (if invalid_query then witness else p);
    }
  }
  
  (* Main reduction procedure *)
  proc guess(gtuple : group list) : bool = {
    var c : ctxt_t; 
    var k : key_t;
    var b' : bool;
    var x_exp : exp;

    (* Parse q-DDH challenge: gtuple = [g^x, g^{x^2}, ..., g^{x^q}, g^r, T] *)
    gxs <- take q gtuple;             (* Extract [g^x, ..., g^{x^q}] *)
    c <- nth witness gtuple q;        (* Extract g^r (ciphertext) *)  
    k <- nth witness gtuple (q + 1);  (* Extract T (challenge key) *)
    
    (* Initialize internal oracle *)
    O_Internal.init(witness);
    
      (* Set initial state: adversary has seen g and g^x *)
    l <-   head witness gxs :: g::  [];
    (* Corresponding representations in basis (g::gxs) *)
    reps <- (* g = g^1 * (g^x)^0 * ... *)
      (zero :: one :: nseq (q-1) zero) ::[(one :: nseq q zero)];  (* g^x = g^0 * (g^x)^1 * ... *)

   
    
    (* Run IND-CCA1 adversary *)
    A(O_Internal).scout(head witness gxs);      (* Scout phase *)
    b' <@ A(O_Internal).distinguish(k, c);     (* Challenge phase *)
    
    return b';
  }
}.

 
(** Alternative adversary construction **)
module (B_from_qDDH (A  : A_qDDH) : Adv_INDCCA1)(O : Oracles_CCA1i) = {
  var gxs : group list

  (* Scout phase: build up powers of x using decryption oracle *)
  proc scout(pk:pk_t) : unit ={
     var i   : int;
     var p   : key_t option;
     gxs <- [pk];  
     i <- 1 ;

     while (i <= q-1) {
     
     p <@ O.dec(last witness gxs, ( one :: nseq i zero));
     
     gxs <- gxs ++ [oget p];
     i <- i + 1;
   }}

    
  
  (* Convert to q-DDH challenge *)
   proc distinguish(k: key_t, c: ctxt_t) : bool = {
      var b'  : bool;
      
      (* Pass challenge to q-DDH adversary *)
      b' <@ A.guess( gxs ++ [c] ++ [k]);
      return b';
   }
}.

declare module A <: A_qDDH {-O_CCA1_Limited, -B_from_qDDH}.

(* Reduction to QDDH from INDCCA *)
lemma INDCCA1_ElGamal_Implies_qDDH &m :
  Pr[QDDH(A).main() @ &m :res] = Pr[IND_CCA1_P(ElGamal,B_from_qDDH(A)).main() @ &m : res].
proof.
  byequiv. proc. inline *. 
  auto.     call(_:true). wp.

   (* align random variable sampling *)
  swap{2} 17 -13. swap{2} 15 -13. swap{2} 17 -13. swap{1} 4 -1.  wp.



  
  (* Entering while loop where g_tuple is formed *)


while {2} (
  1 <= i{2} <= q  /\
  (B_from_qDDH.gxs{2} =  map (fun j => g ^ exp sk{2} j) (range 1 (i{2}+1))) /\
  O_CCA1_Limited.l{2} = ( rev ( B_from_qDDH.gxs{2}) ++ [g]) /\
  (* Oracle state *)
  O_CCA1_Limited.sk{2} = sk{2}  /\
  size O_CCA1_Limited.qs{2} < i{2}) (q  - i{2}).

  auto. progress. smt().  smt().
    have help_map_range : map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 2)) =
    map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 1)) ++ [g ^ exp sk{hr} (i{hr} + 1)].
    have range_split: range 1 (i{hr} + 2) = range 1 (i{hr} + 1) ++ [i{hr} + 1].
  smt(@List).

rewrite range_split.
rewrite map_cat.
simplify. smt(). rewrite help_map_range. congr.
    have range_nonempty: 1 < i{hr} + 1 by smt(). congr.
have range_list_nonempty: range 1 (i{hr} + 1) <> []. 
  smt(@List).

have last_map: 
  last witness (map (fun j => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) = 
    g ^ exp sk{hr} (last witness (range 1 (i{hr} + 1))). 

    smt(@List gt0_q).
 

have last_range: 
  last witness (range 1 (i{hr} + 1)) = i{hr}.
    smt(@List). rewrite last_map last_range. smt(@ZModE @List @G @GP gt0_q).




    pose L := map (fun j => g ^ exp sk{hr} j) (range 1 (i{hr} + 1)).
    pose x := last witness L.





    smt(gt0_q @List).

    smt(). smt(). smt(). smt(gt0_q). 



  







    elim H3 => H3. smt(). 
have opp_case : last witness
      (map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) =
    prodEx
      (rev (map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) ++
       [g]) (one :: nseq i{hr} zero).
have left_eq: last witness (map (fun j => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) = g ^ exp sk{hr} i{hr}.
rewrite -nth_last size_map size_range.
  have ->: max 0 (i{hr} + 1 - 1) = i{hr} by smt().
have idx_valid: 0 <= i{hr} - 1 < size (range 1 (i{hr} + 1)).
- rewrite size_range.
  have ->: max 0 (i{hr} + 1 - 1) = i{hr} by smt().
  smt(). 
  rewrite (nth_map witness witness).
- exact idx_valid.
- (* 现在证明 nth witness (range 1 (i{hr} + 1)) (i{hr} - 1) = i{hr} *)
  rewrite nth_range.
  + smt().
    smt(). 

     have right_eq : prodEx
  (rev (map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) ++ [g])
  (one :: nseq i{hr} zero) = g ^ exp sk{hr} i{hr}. search rev.  rewrite -map_rev. have ->: (rev (range 1 (i{hr} + 1))) = i{hr} :: (rev (range 1 (i{hr}))) by smt(@List).
    rewrite map_cons.
 rewrite /=. rewrite prodExConsGeneral. rewrite  prodEx_nseq_zero. smt(). smt(@ZModE @G @GP). smt(). smt().






have opp_case : last witness
      (map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) =
    prodEx
      (rev (map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) ++
       [g]) (one :: nseq i{hr} zero).
have left_eq: last witness (map (fun j => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) = g ^ exp sk{hr} i{hr}.
rewrite -nth_last size_map size_range.
  have ->: max 0 (i{hr} + 1 - 1) = i{hr} by smt().
have idx_valid: 0 <= i{hr} - 1 < size (range 1 (i{hr} + 1)).
- rewrite size_range.
  have ->: max 0 (i{hr} + 1 - 1) = i{hr} by smt().
  smt(). 
  rewrite (nth_map witness witness).
- exact idx_valid.
- (* 现在证明 nth witness (range 1 (i{hr} + 1)) (i{hr} - 1) = i{hr} *)
  rewrite nth_range.
  + smt().
    smt(). 

     have right_eq : prodEx
  (rev (map (fun (j : int) => g ^ exp sk{hr} j) (range 1 (i{hr} + 1))) ++ [g])
  (one :: nseq i{hr} zero) = g ^ exp sk{hr} i{hr}. search rev.  rewrite -map_rev. have ->: (rev (range 1 (i{hr} + 1))) = i{hr} :: (rev (range 1 (i{hr}))) by smt(@List).
    rewrite map_cons.
 rewrite /=. rewrite prodExConsGeneral. rewrite  prodEx_nseq_zero. smt(). smt(@ZModE @G @GP). smt(). smt().

















      smt(). smt(gt0_q).  
     auto. progress. swap{1} 3 1. rnd.   swap{2} 4 1. 
rnd  (fun z => g ^ (z + sk0{2} * y{2}))(fun k' => loge k' - sk0{2} * y{2}). wp. rnd.  rnd.
auto. progress. smt(@ZModE @G @GP).  rewrite /dkeym Distr.dmap1E.
rewrite /(\o) /pred1.
(* use distribution *)
rewrite (dt_funi (loge k'R - xL * rL) (loge k'R)).
congr.
apply fun_ext. move => x.
apply eq_iff; split.
(* ：if g^x = k'R，x = loge k'R *)
move=> gx_eq_kR.
rewrite -gx_eq_kR. 
have x_eq: x = loge (g^x) by rewrite GP.loggK.
rewrite gx_eq_kR in x_eq.  smt(@GP).
(* if x = loge k'R then g^x = k'R *)
move=> x_eq_log.
rewrite x_eq_log.
rewrite GP.expgK.
    reflexivity. rewrite /dkeym. rewrite Distr.supp_dmap. exists (zL + xL * rL).
    split. smt(@ZModE). reflexivity. smt(@ZModE @G @GP). smt(gt0_q).





have range_12: range 1 2 = [1] by smt(@List). 
rewrite range_12.

simplify.  

congr.
rewrite /exp.
rewrite iterop1.
smt(@ZModE). 


    smt().  congr. have ->: i_R = q. smt().  smt(). clear H6. elim bL; simplify. algebra. algebra. smt(). smt(). smt().
qed.






declare module B <: Adv_INDCCA1 {-O_CCA1_Limited, -A_from_INDCCA1}.
 



(* Reduction to INDCCA from QDDH *)
lemma qDDH_Implies_INDCCA1_ElGamal &m :
  Pr[IND_CCA1_P(ElGamal,B).main() @ &m : res] = 
  Pr[QDDH(A_from_INDCCA1(B)).main() @ &m : res].
  proof.
    byequiv => //.
    proc. inline*. swap{1} 11 -9. swap{1} 14 -10.  auto. call(_ : true).

    (* bring random coins to front *)
    swap{1} 14 -9.  swap{2} 3 2.    swap{1} 4 -1.  wp.


  


  
    (* show that scout is equal on both sides - including decryption oracle response *)

    call (_ : 
    (* Condition 1: Query list consistency between games *)
    (IND_CCA1_P.OS.l{1} = A_from_INDCCA1.l{2})
    
    (* Condition 2: Query count consistency between oracles *)
    /\ (size O_CCA1_Limited.qs{1} = size A_from_INDCCA1.O_Internal.qs{2})
    
    (* Condition 3: Non-negative query count invariant *)
    /\ (0 <= size O_CCA1_Limited.qs{1})
    
    (* Condition 4: Representation-to-ciphertext mapping consistency
       The reduction's ciphertext list equals the product of bases with representations *)
    /\ (A_from_INDCCA1.l{2} = map (fun y => prodEx (g :: A_from_INDCCA1.gxs{2}) y) A_from_INDCCA1.reps{2})
    
    (* Condition 5: Base elements construction from secret key
       The reduction's base list is constructed as powers of g using the secret key *)
    /\ A_from_INDCCA1.gxs{2} = map (fun i => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q+1))
    
    (* Condition 6: Uniform representation size constraint
       All representation vectors have the required size q+1 *)
    /\ all (fun rep => size rep = q + 1) A_from_INDCCA1.reps{2}
    
    (* Condition 7: Trailing zeros constraint for valid representations
       Each representation has trailing zeros after the query-dependent prefix *)
    /\ all (fun rep => drop (size A_from_INDCCA1.reps{2}) rep = nseq (q+1-(size A_from_INDCCA1.reps{2})) zero)
           A_from_INDCCA1.reps{2}
    
    (* Condition 8: Representation count relationship
       The number of representations equals the number of queries plus 2 (for challenge) *)
    /\ size A_from_INDCCA1.reps{2} = size O_CCA1_Limited.qs{1} + 2
  ).
  

 
      proc.
      inline{1} ElGamal.dec.
      case (c{2} <> prodEx (A_from_INDCCA1.l{2}) z{2}).
      auto. progress. smt(). smt(). smt(). smt(). smt(). smt(). 



      smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().  smt(). smt(). smt().
      smt(). 
      auto. progress. 
      rewrite H4. simplify.



      (* Apply q0_simp to handle the q=0 case and prodExScale2 for scalar multiplication *)
      rewrite q0_simp prodExScale2. rewrite size_map.
      (* Key transformation: convert map of prodEx to prodEx of summed representations
         This applies the fundamental lemma ex_map_prodEx which shows that:
         prodEx(map(prodEx(bases, ·), reps), z) = prodEx(bases, shift_trunc(sumv(scalev_map(reps, z))))
         The size arguments (q+1) and (size reps) ensure the transformation is valid *)
      rewrite (ex_map_prodEx _ _ (q+1 ) (size A_from_INDCCA1.reps{2})).
      rewrite size_map. rewrite size_range.
      smt(@List @GP gt0_q). trivial. rewrite ex_range_shift.
      pose bases :=  (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 2))).
      pose reps :=  A_from_INDCCA1.reps{2}.
      pose z := z{2}.




      (* Key lemma: flatten nested prodEx operations using distributivity
         This establishes that prodEx distributes over map and can be "flattened":
         prodEx(map(prodEx(bases, ·), reps), z) = prodEx(bases, sumv(scalev_map(reps, z)))
   
        Left side: Apply prodEx to each rep with bases, then combine with z
        Right side: First combine reps with z using scalar multiplication, sum them, then apply prodEx
   
        This transformation is fundamental for the reduction's correctness *)



  
      have flat :  prodEx (map (prodEx bases) reps) z
      = prodEx bases (sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z))).
      have reps_all_size: all (fun rep => size rep = q + 1) reps. exact H1.
      elim: reps z reps_all_size => [|rep reps IH] [|z_head z_tail] reps_size //=.  
      rewrite prodEx_nil.  rewrite sumv_nil. 
      rewrite /zerov. rewrite prodEx_nseq_zero. smt(gt0_q) . smt().
      rewrite prodEx_nil_l. rewrite sumv_nil.  rewrite /zerov. rewrite prodEx_nseq_zero. smt(gt0_q). smt().
      rewrite prodEx_nil_r. rewrite sumv_nil.  rewrite /zerov. rewrite prodEx_nseq_zero. smt(gt0_q). smt().
      rewrite prodExConsGeneral. rewrite sumv_cons. rewrite prodEx_addv_distributive.  rewrite /scalev.
      rewrite size_map. have size_bases: size bases = q + 1.
      rewrite /bases size_map size_range. smt(@List @GP gt0_q).
      have size_rep : size rep = q +1.  smt(@G @GP). smt(). 
      have sumv_size: size (sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2)
          (zip reps z_tail))) = q + 1.
      case: (reps = []) => [reps_empty | reps_nonempty].
       - rewrite reps_empty /=. rewrite zip_nil_l.   rewrite  sumv_nil. rewrite /zerov size_nseq. smt(gt0_q).
       - apply size_sumv.
       move=> v /mapP [pair [pair_in ->]].
       case: pair pair_in => [rep_elem z_elem] /= pair_in_zip.
       rewrite size_scalev. have: rep_elem \in reps by smt(@List).  smt(@G @GP @List). rewrite sumv_size.
       have size_bases: size bases = q + 1.
       rewrite /bases size_map size_range.
       smt(@List @GP gt0_q). smt().
       congr. rewrite prodExScale1.
       trivial. rewrite IH. smt(). trivial. rewrite flat.
      



       rewrite /bases. 
       pose exps := (sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2)(zip reps z))).
       have size_exps_analysis: size exps = q + 1.  rewrite /exps. 
       rewrite size_sumv.
       move=> v v_in_map. move: v_in_map => /mapP [x [x_in_zip v_eq]]. rewrite v_eq. 
       move: x_in_zip => /mem_zip_fst. rewrite -v_eq /= => x1_in_reps. rewrite v_eq.
       rewrite  size_scalev. by move: H1 => /allP /(_ x.`1 x1_in_reps). smt().
       have cond :size exps < q+2. smt().









      (* start to prove the last element of exps is zero*)

      have drop_last_ele : drop q exps = nseq 1 zero.
      rewrite /exps.
      (* the exps is a list of list, we first need to prove the last element of each element of zip exps z  should be 0*)
      have all_elements_zero_suffix:
      forall u, u \in map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z)
      => drop q u = nseq 1 zero.
      move=> u u_in_map.
      have: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2. smt(@List).
      case=> [[rep z_elem]] [pair_in_zip u_def].
      (* the exps is a list of list, we  need to prove the last element of each element of  exps   should be 0*)
      have rep_zero_suffix: drop (size A_from_INDCCA1.reps{2}) rep =
                            nseq (q + 1 - (size A_from_INDCCA1.reps{2})) zero.
      move : H2. rewrite allP. move=> H2_expanded. apply H2_expanded.
      smt(@List).
      have size_qs_le_q: size O_CCA1_Limited.qs{1} <= q.
      smt().
      rewrite u_def.
      rewrite drop_scalev. simplify.  have rep_size: size rep = q + 1.

      smt(@List).
      have drop_q_rep: drop q rep = [nth witness rep q]. smt(@List @G @GP gt0_q).
      have nth_q_zero: nth witness rep q = zero.
      have:  size O_CCA1_Limited.qs{1} <= q by exact size_qs_le_q. move => h.






      
      have: nth witness rep q =
            nth witness (nseq (q + 1 - (size A_from_INDCCA1.reps{2})) zero) (q - (size A_from_INDCCA1.reps{2})).   
      smt(@List @G @GP gt0_q).
      smt(@List @G @GP gt0_q).
      rewrite drop_q_rep nth_q_zero.
      have one_zero : [zero] = nseq 1 zero. smt(@G @GP @List). rewrite one_zero.
      
      rewrite scalev_nseq_zero. trivial. (* prove the all elemnts zero suffix *)








      
      have all_form: all (fun u => drop q u = nseq 1 zero) 
      (map (fun  (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z)).
      apply/allP => u u_in_map. exact (all_elements_zero_suffix u u_in_map).  move : all_form.



      
       pose mapped_list := map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z).
       move=> all_form.


       case (mapped_list = []). move =>map_empty. rewrite map_empty. rewrite sumv_nil. rewrite /zerov. rewrite drop_nseq.  smt(). smt().
       move => mapped_npnempty.
       have tran : drop q (sumv mapped_list)  = sumv(map (drop q) ( mapped_list)). rewrite drop_sumv.
       smt(). rewrite /mapped_list. apply/allP => u u_in_mapped.
       have: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2. apply/mapP. by [].
       case => pair [pair_in_zip u_eq].

       rewrite u_eq. rewrite /=. rewrite size_scalev.

       have pair_first_in_reps: pair.`1 \in reps.

       smt(@List). have: (fun (rep : ZModE.exp list) => size rep = q + 1) pair.`1.  smt(allP). by[]. smt(). smt(@List).               
       rewrite tran. 
       have map_all_zero: map (drop q) mapped_list = nseq (size mapped_list) (nseq 1 zero). 

      
       apply (eq_from_nth witness).
       rewrite size_map size_nseq.
       case: (0 <= size mapped_list) => [ge0_size|lt0_size]. smt(@List).

       + smt(@List).

       move=> i hi.
       rewrite size_map in hi.  rewrite (nth_map witness) //. rewrite nth_nseq_if.

       case: (0 <= i < size mapped_list) => [valid_i|invalid_i].
       have u_in_mapped: nth witness mapped_list i \in mapped_list.
       by apply mem_nth.
       have u_drop_zero: drop q (nth witness mapped_list i) = nseq 1 zero. smt(@List @GP).
       by rewrite u_drop_zero.
       smt(). rewrite map_all_zero.  have map_ge1: 1<= size mapped_list  by smt(@List).
       rewrite sumv_nseq_zero_singleton. smt(). trivial. (* end of drop_last_ele :prove the last element is 0*)



       rewrite prodExShiftTrunce. rewrite size_map size_range. smt(gt0_q).
       apply size_exps_analysis. smt().


      (* here we want to prove drop q exps is same as nth witness exps q*)
       have last_exp_zero: nth witness exps q = zero.
       have: drop q exps = [zero].
       rewrite drop_last_ele.
       have nseq_one_zero: nseq 1 zero = [zero]. smt(@List). smt(@List). 
       move=> drop_eq.
       have: size (drop q exps) = 1.
       rewrite drop_eq. smt(@List).
       have: nth witness (drop q exps) 0 = zero.
       rewrite drop_eq. smt(@List).
       have: nth witness exps q = nth witness (drop q exps) 0.
       rewrite nth_drop.
       smt(). smt(). smt(). smt().    (* prove the last element of exps is zero*)

       rewrite prodEx_split_last_zero. rewrite size_map size_range.


       smt(@G @GP @List gt0_q). smt(). rewrite -last_exp_zero. smt(). (* here we need to prove nth witness exps (size exps - 1) = zero by last_exp_zero*)
      
        rewrite size_map size_range. have max_qplus : (max 0 (q + 2 - 1) - 1) = q by smt(gt0_q).
        rewrite max_qplus. rewrite -map_take.
        (* use the def of zip, change  range (0,q+2) to (1 q+1)*)
      
        have take_range : take q (range 1 (q + 2)) = range 1 (q+1).
      
        have range_split: range 1 (q + 2) = range 1 (q + 1) ++ [q + 1].
        smt(@List). rewrite range_split. rewrite take_cat. rewrite size_range.
        have case_nop :  !(q < max 0 (q + 1 - 1)) by smt(gt0_q). rewrite case_nop. simplify.
        have case_not:(q - max 0 q <= 0) by smt( gt0_q). rewrite case_not. simplify.
        smt(@List). rewrite take_range.  rewrite behead_drop. rewrite -map_drop.
        have drop_range :  (drop 1 (range 0 (q + 1))) = (range 1 (q+1)). smt(@List gt0_q). rewrite drop_range. 
        have last_eq : prodEx
        (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 1)))
        exps = prodEx
        (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 1)))
        (take (size exps - 1) exps).
     rewrite prodEx_sizele. rewrite size_map size_range. rewrite size_exps_analysis.


     smt(gt0_q @GP @ZModE). rewrite size_map size_range. smt(gt0_q). rewrite last_eq. trivial.

        

      (* Apply q0_simp to handle the q=0 case and prodExScale2 for scalar multiplication *)
      rewrite q0_simp prodExScale2. rewrite size_map.
      (* Key transformation: convert map of prodEx to prodEx of summed representations
         This applies the fundamental lemma ex_map_prodEx which shows that:
         prodEx(map(prodEx(bases, ·), reps), z) = prodEx(bases, shift_trunc(sumv(scalev_map(reps, z))))
         The size arguments (q+1) and (size reps) ensure the transformation is valid *)
      rewrite (ex_map_prodEx _ _ (q+1 ) (size A_from_INDCCA1.reps{2})).
      rewrite size_map. rewrite size_range.
      smt(@List @GP gt0_q). trivial. rewrite ex_range_shift.
      pose bases :=  (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 2))).
      pose reps :=  A_from_INDCCA1.reps{2}.
      pose z := z{2}.




      (* Key lemma: flatten nested prodEx operations using distributivity
         This establishes that prodEx distributes over map and can be "flattened":
         prodEx(map(prodEx(bases, ·), reps), z) = prodEx(bases, sumv(scalev_map(reps, z)))
   
        Left side: Apply prodEx to each rep with bases, then combine with z
        Right side: First combine reps with z using scalar multiplication, sum them, then apply prodEx
   
        This transformation is fundamental for the reduction's correctness *)



  
      have flat :  prodEx (map (prodEx bases) reps) z
      = prodEx bases (sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z))).
      have reps_all_size: all (fun rep => size rep = q + 1) reps. exact H1.
      elim: reps z reps_all_size => [|rep reps IH] [|z_head z_tail] reps_size //=.  
      rewrite prodEx_nil.  rewrite sumv_nil. 
      rewrite /zerov. rewrite prodEx_nseq_zero. smt(gt0_q) . smt().
      rewrite prodEx_nil_l. rewrite sumv_nil.  rewrite /zerov. rewrite prodEx_nseq_zero. smt(gt0_q). smt().
      rewrite prodEx_nil_r. rewrite sumv_nil.  rewrite /zerov. rewrite prodEx_nseq_zero. smt(gt0_q). smt().
      rewrite prodExConsGeneral. rewrite sumv_cons. rewrite prodEx_addv_distributive.  rewrite /scalev.
      rewrite size_map. have size_bases: size bases = q + 1.
      rewrite /bases size_map size_range. smt(@List @GP gt0_q).
      have size_rep : size rep = q +1.  smt(@G @GP). smt(). 
      have sumv_size: size (sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2)
          (zip reps z_tail))) = q + 1.
      case: (reps = []) => [reps_empty | reps_nonempty].
       - rewrite reps_empty /=. rewrite zip_nil_l.   rewrite  sumv_nil. rewrite /zerov size_nseq. smt(gt0_q).
       - apply size_sumv.
       move=> v /mapP [pair [pair_in ->]].
       case: pair pair_in => [rep_elem z_elem] /= pair_in_zip.
       rewrite size_scalev. have: rep_elem \in reps by smt(@List).  smt(@G @GP @List). rewrite sumv_size.
       have size_bases: size bases = q + 1.
       rewrite /bases size_map size_range.
       smt(@List @GP gt0_q). smt().
       congr. rewrite prodExScale1.
       trivial. rewrite IH. smt(). trivial. rewrite flat.
      



       rewrite /bases. 
       pose exps := (sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2)(zip reps z))).
       have size_exps_analysis: size exps = q + 1.  rewrite /exps. 
       rewrite size_sumv.
       move=> v v_in_map. move: v_in_map => /mapP [x [x_in_zip v_eq]]. rewrite v_eq. 
       move: x_in_zip => /mem_zip_fst. rewrite -v_eq /= => x1_in_reps. rewrite v_eq.
       rewrite  size_scalev. by move: H1 => /allP /(_ x.`1 x1_in_reps). smt().
       have cond :size exps < q+2. smt().









      (* start to prove the last element of exps is zero*)

      have drop_last_ele : drop q exps = nseq 1 zero.
      rewrite /exps.
      (* the exps is a list of list, we first need to prove the last element of each element of zip exps z  should be 0*)
      have all_elements_zero_suffix:
      forall u, u \in map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z)
      => drop q u = nseq 1 zero.
      move=> u u_in_map.
      have: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2. smt(@List).
      case=> [[rep z_elem]] [pair_in_zip u_def].
      (* the exps is a list of list, we  need to prove the last element of each element of  exps   should be 0*)
      have rep_zero_suffix: drop (size A_from_INDCCA1.reps{2}) rep =
                            nseq (q + 1 - (size A_from_INDCCA1.reps{2})) zero.
      move : H2. rewrite allP. move=> H2_expanded. apply H2_expanded.
      smt(@List).
      have size_qs_le_q: size O_CCA1_Limited.qs{1} <= q.
      smt().
      rewrite u_def.
      rewrite drop_scalev. simplify.  have rep_size: size rep = q + 1.

      smt(@List).
      have drop_q_rep: drop q rep = [nth witness rep q]. smt(@List @G @GP gt0_q).
      have nth_q_zero: nth witness rep q = zero.
      have:  size O_CCA1_Limited.qs{1} <= q by exact size_qs_le_q. move => h.






      
      have: nth witness rep q =
            nth witness (nseq (q + 1 - (size A_from_INDCCA1.reps{2})) zero) (q - (size A_from_INDCCA1.reps{2})).   
      smt(@List @G @GP gt0_q).
      smt(@List @G @GP gt0_q).
      rewrite drop_q_rep nth_q_zero.
      have one_zero : [zero] = nseq 1 zero. smt(@G @GP @List). rewrite one_zero.
      
      rewrite scalev_nseq_zero. trivial. (* prove the all elemnts zero suffix *)








      
      have all_form: all (fun u => drop q u = nseq 1 zero) 
      (map (fun  (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z)).
      apply/allP => u u_in_map. exact (all_elements_zero_suffix u u_in_map).  move : all_form.



      
       pose mapped_list := map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z).
       move=> all_form.


       case (mapped_list = []). move =>map_empty. rewrite map_empty. rewrite sumv_nil. rewrite /zerov. rewrite drop_nseq.  smt(). smt().
       move => mapped_npnempty.
       have tran : drop q (sumv mapped_list)  = sumv(map (drop q) ( mapped_list)). rewrite drop_sumv.
       smt(). rewrite /mapped_list. apply/allP => u u_in_mapped.
       have: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2. apply/mapP. by [].
       case => pair [pair_in_zip u_eq].

       rewrite u_eq. rewrite /=. rewrite size_scalev.

       have pair_first_in_reps: pair.`1 \in reps.

       smt(@List). have: (fun (rep : ZModE.exp list) => size rep = q + 1) pair.`1.  smt(allP). by[]. smt(). smt(@List).               
       rewrite tran. 
       have map_all_zero: map (drop q) mapped_list = nseq (size mapped_list) (nseq 1 zero). 

      
       apply (eq_from_nth witness).
       rewrite size_map size_nseq.
       case: (0 <= size mapped_list) => [ge0_size|lt0_size]. smt(@List).

       + smt(@List).

       move=> i hi.
       rewrite size_map in hi.  rewrite (nth_map witness) //. rewrite nth_nseq_if.

       case: (0 <= i < size mapped_list) => [valid_i|invalid_i].
       have u_in_mapped: nth witness mapped_list i \in mapped_list.
       by apply mem_nth.
       have u_drop_zero: drop q (nth witness mapped_list i) = nseq 1 zero. smt(@List @GP).
       by rewrite u_drop_zero.
       smt(). rewrite map_all_zero.  have map_ge1: 1<= size mapped_list  by smt(@List).
       rewrite sumv_nseq_zero_singleton. smt(). trivial. (* end of drop_last_ele :prove the last element is 0*)



       rewrite prodExShiftTrunce. rewrite size_map size_range. smt(gt0_q).
       apply size_exps_analysis. smt().


      (* here we want to prove drop q exps is same as nth witness exps q*)
       have last_exp_zero: nth witness exps q = zero.
       have: drop q exps = [zero].
       rewrite drop_last_ele.
       have nseq_one_zero: nseq 1 zero = [zero]. smt(@List). smt(@List). 
       move=> drop_eq.
       have: size (drop q exps) = 1.
       rewrite drop_eq. smt(@List).
       have: nth witness (drop q exps) 0 = zero.
       rewrite drop_eq. smt(@List).
       have: nth witness exps q = nth witness (drop q exps) 0.
       rewrite nth_drop.
       smt(). smt(). smt(). smt().    (* prove the last element of exps is zero*)

       rewrite prodEx_split_last_zero. rewrite size_map size_range.


       smt(@G @GP @List gt0_q). smt(). rewrite -last_exp_zero. smt(). (* here we need to prove nth witness exps (size exps - 1) = zero by last_exp_zero*)
      
        rewrite size_map size_range. have max_qplus : (max 0 (q + 2 - 1) - 1) = q by smt(gt0_q).
        rewrite max_qplus. rewrite -map_take.
        (* use the def of zip, change  range (0,q+2) to (1 q+1)*)
      
        have take_range : take q (range 1 (q + 2)) = range 1 (q+1).
      
        have range_split: range 1 (q + 2) = range 1 (q + 1) ++ [q + 1].
        smt(@List). rewrite range_split. rewrite take_cat. rewrite size_range.
        have case_nop :  !(q < max 0 (q + 1 - 1)) by smt(gt0_q). rewrite case_nop. simplify.
        have case_not:(q - max 0 q <= 0) by smt( gt0_q). rewrite case_not. simplify.
        smt(@List). rewrite take_range.  rewrite behead_drop. rewrite -map_drop.
        have drop_range :  (drop 1 (range 0 (q + 1))) = (range 1 (q+1)). smt(@List gt0_q). rewrite drop_range. 
        have last_eq : prodEx
        (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 1)))
        exps = prodEx
        (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 1)))
        (take (size exps - 1) exps).
     rewrite prodEx_sizele. rewrite size_map size_range. rewrite size_exps_analysis.


     smt(gt0_q @GP @ZModE). rewrite size_map size_range. smt(gt0_q). rewrite last_eq. trivial. 


     (*start to provve next goal*)
     smt(). smt(gt0_q).

      rewrite /shift_trunc.   rewrite size_take. smt(gt0_q).
      simplify.
      pose bases :=  (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 2))).
      pose reps :=  A_from_INDCCA1.reps{2}.
      pose z := z{2}. rewrite /bases.
      pose exps := (sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2)(zip reps z))). 


      (* want to prove size exps is equal to q+1*)
      have size_exps_analysis: size exps = q + 1.  rewrite /exps. 
      rewrite size_sumv.
      move=> v v_in_map. move: v_in_map => /mapP [x [x_in_zip v_eq]]. rewrite v_eq. 
      move: x_in_zip => /mem_zip_fst. rewrite -v_eq /= => x1_in_reps. rewrite v_eq.
      rewrite  size_scalev. by move: H1 => /allP /(_ x.`1 x1_in_reps). smt(). (* size prove end*)
      have cond :size exps < q+2. smt(). rewrite -size_exps_analysis /exps.
      smt().
      rewrite /shift_trunc.
      pose bases :=  (map (fun (i : int) => g ^ exp O_CCA1_Limited.sk{1} i) (range 1 (q + 2))).
      pose reps :=  A_from_INDCCA1.reps{2}.
      pose z := z{2}. rewrite /bases.
      pose exps := sumv (map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip A_from_INDCCA1.reps{2} z{2})).

      have take_zero_exps: take (q + 1) (zero :: exps) = zero :: take q exps.
      rewrite take_cons.
      case: (q + 1 <= 0) => [le0_q1|gt0_q1].
      - smt().
      - simplify.
    
      smt().





        
rewrite take_zero_exps.
have drop_step: drop (1 + size reps) (zero :: take q exps) = 
                drop (size reps) (take q exps). smt(@List).
rewrite drop_step.
have exps_split: exps = take q exps ++ drop q exps. by rewrite cat_take_drop.



        


     have drop_q_zero: drop q exps = nseq 1 zero. (*start to prove the last element of exps is zero*)
     rewrite /exps.
        (* have all suffix is zero*)
      have all_elements_zero_suffix:
      forall u, u \in map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z)
      => drop q u = nseq 1 zero.
      move=> u u_in_map.
      have: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2. apply/mapP.
      exact u_in_map.



      case=> [[rep z_elem]] [pair_in_zip u_def].




      
      have rep_zero_suffix: drop (size A_from_INDCCA1.reps{2}) rep = nseq (q + 1 -  size A_from_INDCCA1.reps{2}) zero.
      move : H2. rewrite allP. move=> H2_expanded. apply H2_expanded.
      smt(@List).
      have size_qs_le_q:  size A_from_INDCCA1.reps{2} <= q.
      smt().
      rewrite u_def.
      rewrite drop_scalev. simplify.  have rep_size: size rep = q + 1.

      smt(@List).
      have drop_q_rep: drop q rep = [nth witness rep q]. smt(@List @G @GP gt0_q).
      have nth_q_zero: nth witness rep q = zero.
      have:   size A_from_INDCCA1.reps{2} <= q by exact size_qs_le_q.
      have: nth witness rep q =
            nth witness (nseq (q + 1 -  size A_from_INDCCA1.reps{2}) zero) (q -  size A_from_INDCCA1.reps{2}).
      

      smt(@List @G @GP gt0_q).   smt(@List @G @GP gt0_q).  rewrite drop_q_rep nth_q_zero.
       have one_zero : [zero] = nseq 1 zero. smt(@G @GP @List). rewrite one_zero.
      
      rewrite scalev_nseq_zero. trivial. (*end of proving all_eleents_zero_suffix*)


        rewrite -/reps.
        pose mapped_list := map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z). 
        case (mapped_list = []). move =>map_empty.
        rewrite map_empty. rewrite sumv_nil. rewrite /zerov. rewrite drop_nseq. smt(). smt().
        move => mapped_npnempty.
       (* proving the tran which is imporatant to change the position of drop and sumv*)
        have tran : drop q (sumv mapped_list)  = sumv(map (drop q) ( mapped_list)). rewrite drop_sumv. smt().
        rewrite /mapped_list. apply/allP => u u_in_mapped.
        have: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2. apply/mapP. by [].
        case => pair [pair_in_zip u_eq].
        rewrite u_eq. rewrite /=. rewrite size_scalev.
        have pair_first_in_reps: pair.`1 \in reps.
        smt(@List). have: (fun (rep : ZModE.exp list) => size rep = q + 1) pair.`1.
        smt(allP). by[]. smt(). smt(@List).  rewrite tran. 

        (* proving the mapped list end with size itself - q zero*)
        have map_all_zero: map (drop q) mapped_list = nseq (size mapped_list) (nseq 1 zero). 
                   
        apply (eq_from_nth witness).
      
        rewrite size_map size_nseq.
        case: (0 <= size mapped_list) => [ge0_size|lt0_size]. smt(@List).
       + smt(@List).
        move=> i hi.
        rewrite size_map in hi.
        rewrite (nth_map witness) //.
        rewrite nth_nseq_if.
        case: (0 <= i < size mapped_list) => [valid_i|invalid_i].
        have u_in_mapped: nth witness mapped_list i \in mapped_list.
        by apply mem_nth.
        have u_drop_zero: drop q (nth witness mapped_list i) = nseq 1 zero. smt(@List @GP).
        by rewrite u_drop_zero.
        smt(). rewrite map_all_zero.  have map_ge1: 1<= size mapped_list  by smt(@List).   rewrite sumv_nseq_zero_singleton. smt(). trivial. (* end of proving drop_q_zero*)

        (*going to simplify the rhs*)
        have rhs_simp: q + 1 - (1 + size reps) = q - size reps. smt(). rewrite rhs_simp.

        
        have exps_structure: exps = take q exps ++ [zero]. smt(@GP @List @G).
        have take_size: size (take q exps) = q.
        rewrite size_take.
        have exps_size: size exps = q + 1.
        rewrite exps_structure size_cat.





        smt(@GP @G @List).
        smt(gt0_q).
        smt(gt0_q @List @GP @G).

       








        apply (eq_from_nth witness).
        rewrite size_drop. smt(gt0_q). smt(@G @GP @List).
        move=> i hi.
        rewrite size_drop  in hi. smt(gt0_q). rewrite  take_size in hi.
        rewrite nth_drop. smt(). smt().
        have max_qqs: max 0 (q - size reps) = q - size reps by smt(gt0_q).


        move :hi. rewrite max_qqs. move => hi.


        rewrite nth_nseq_if. rewrite hi. simplify. 
      
        have pos_valid: size reps + i < q.
        smt(gt0_q).


      have exps_at_pos: nth witness (take q exps) (size reps + i) = 
                     nth witness exps (size reps + i).
      rewrite nth_take //.
      smt(gt0_q).
    
      rewrite exps_at_pos. 
      (* we want to prove all last elements of elements in exps is 0*)
      have all_components_zero: forall u, u \in map (fun  (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2)
                               (zip reps z) => nth witness u (size reps + i) = zero.
      move=> u u_in_mapped.
      have [pair [pair_in_zip u_eq]]: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2.
      move: u_in_mapped.
      elim: (zip reps z) => [|hd tl ih]. rewrite /=. smt(). rewrite /=. smt(@List).
      rewrite u_eq. 
      have rep_in_reps: pair.`1 \in reps.
      smt(@List @G @GP).
      rewrite /scalev.
      have map_nth: nth witness (map (fun x => x * pair.`2) pair.`1) (size reps+ i) = 
              (nth witness pair.`1 (size reps + i)) * pair.`2.
  (* index is valid *)
  have valid_idx: size reps + i < size pair.`1.
  have rep_size: size pair.`1 = q + 1.
  smt( @List).
  smt(gt0_q @List).
  
  (* use nth_map *)
   rewrite (nth_map witness) //. smt(@G @List gt0_q).
   rewrite map_nth.
   have rep_zero: nth witness pair.`1 (size reps + i) = zero.
   (* by H2 *)
   have rep_drop: drop (size reps) pair.`1 = nseq (q + 1 - size reps) zero.
   smt( @List gt0_q).
   have: nth witness pair.`1 (size reps + i) = nth witness (drop (size reps) pair.`1) i.
   rewrite nth_drop.
   have rep_size: size pair.`1 = q + 1.
   smt(@List). smt(). smt(). smt().
  
  
  rewrite rep_drop nth_nseq. smt(gt0_q @List). smt(). 
                rewrite rep_zero. smt(@ZModE @G @GP).
                rewrite /exps.
                rewrite -/reps.
                pose reps_size := size reps.
                pose mapped_list := map (fun (x : ZModE.exp list * ZModE.exp) => scalev x.`1 x.`2) (zip reps z).

                case: (mapped_list = []) => [map_empty|map_nonempty].
                rewrite map_empty.
                rewrite sumv_nil /zerov nth_nseq. smt(@List @G gt0_q). trivial. (* end proving all components zero*)



(*start to proof all nth size all nth zero*)
                have all_nth_zero: forall u, u \in mapped_list => nth witness u (reps_size + i) = zero.
                exact all_components_zero.

                have all_nth_size: forall u, u \in mapped_list => size u  = q+1.
                move=> u u_in_mapped.
                have [pair [pair_in_zip u_eq]]: exists pair, pair \in zip reps z /\ u = scalev pair.`1 pair.`2.
                apply/mapP.
                exact u_in_mapped.
                have rep_in_reps: pair.`1 \in reps.
                smt(@List).

                have rep_size: size pair.`1 = q + 1.
                smt( @List).
                rewrite u_eq.
                rewrite size_scalev.
                exact rep_size.
 (*end*)




      elim: mapped_list all_nth_zero all_nth_size map_nonempty => [|hd tl ih] all_zero all_size  map_ne.
      by [].
      case: (tl = []) => [tl_empty|tl_nonempty].
      rewrite tl_empty /sumv /= /foldr /=.
    (* sumv [hd] = addv hd zerov = hd *)
      have addv_zerov_eq: addv hd zerov = hd.
      rewrite /addv /zerov.
      apply (eq_from_nth zero).
      rewrite size_map size_zip size_nseq.
      have hd_size: size hd = q + 1. smt(@GP@List). smt(@GP @List gt0_q).
      move=> i0 hi0.
      rewrite (nth_map (zero, zero)).
      rewrite size_zip size_nseq.
      have hd_size: size hd = q + 1.
      apply all_size.
      by left.
      smt(gt0_q @List @GP). rewrite nth_zip.

   (* prove i0 < min (size hd) (size (nseq (q + 1) zero)) *)
    have hd_size: size hd = q + 1.
    apply all_size.
    by left.
    rewrite size_nseq hd_size.
    smt(gt0_q). simplify.
    rewrite nth_nseq_if. simplify. smt(@ZModE @G @GP). rewrite addv_zerov_eq. apply all_zero. smt(@List).
    rewrite /=.
    have hd_size: size hd = q + 1.
    apply all_size.
    by left.  have sumv_tl_size: size (sumv tl) = q + 1. rewrite size_sumv. smt(). smt(). rewrite sumv_cons.
  
(* use addv_nth *)
    rewrite addv_nth. smt(). smt().
    have: nth witness hd (reps_size + i) = zero by apply all_zero; left.
    have: nth witness (sumv tl) (reps_size + i) = zero.
    apply ih => //.
  - move=> u u_in_tl; apply all_zero; right; exact u_in_tl.
  - move=> u u_in_tl; apply all_size; right; exact u_in_tl.
    smt(@ZModE). 























    apply/allP => rep rep_in_reps. simplify.

    (* get from H2 *)
    have rep_drop: drop (size A_from_INDCCA1.reps{2}) rep = nseq (q + 1 - size A_from_INDCCA1.reps{2}) zero.
    smt(gt0_q @List).

    have rep_size: size rep = q + 1.
    smt(gt0_q @List).

   (* we want to do sth on rhs*)
   have drop_compose: drop (1 + size A_from_INDCCA1.reps{2}) rep = drop 1 (drop (size A_from_INDCCA1.reps{2}) rep).
   rewrite -drop_drop. smt(). smt(gt0_q). trivial.


   rewrite drop_compose rep_drop.
   have rhs_simp: q + 1 - (1 + size A_from_INDCCA1.reps{2}) = q - size A_from_INDCCA1.reps{2}.
   smt(). rewrite rhs_simp.
  (* use drop_nseq *)
   rewrite drop_nseq.
   smt(gt0_q).

congr.
smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt(). smt().  smt(). smt(). smt().




















      
  (*end proving orcales are equal second part of prove*)
  
  auto. progress.
  (* Apply random variable transformation: transform k' to z = loge k' - sk0{1} * y{1},
  with inverse transformation k' = g^(z + sk0{1} * y{1}), converting randomness from
  group elements to exponent field *)
  rnd (fun k' => loge k'- sk0{1} * y{1}) (fun z =>  g ^ (z + sk0{1} * y{1} )). auto. progress.
  smt(@GP).
  rewrite /dkeym  Distr.dmap1E.   
  rewrite /(\o) /pred1.   rewrite (dt_funi zR (zR + sk0L * yL)).
  congr.  apply fun_ext. move => x.  apply eq_iff; split. move=> gx_eq_kR. rewrite gx_eq_kR.
  have x_eq: x = loge (g^x) by rewrite GP.loggK. rewrite gx_eq_kR in x_eq.     

  smt(@GP). move=> h. rewrite /pred1. move: h. smt(@GP). smt(@GP). 
  rewrite take_cat. rewrite size_cat /=. 
  have size_map: size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) = q.
  rewrite size_map size_range.
  smt(@List gt0_q).
  have cond_true: q < size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) + 1.
  rewrite size_map.
  smt().
  rewrite cond_true.
  simplify.
  rewrite take_cat size_map.
  have: q <= q by smt().
  move=> H_q_le_q.
  have q_not_lt_q: !(q < q) by smt().
  rewrite q_not_lt_q /=.
  rewrite cats0.
  have range_structure: range 1 (q + 1) = 1 :: (range 2 (q + 1)).
  by smt(@List gt0_q). rewrite range_structure map_cons head_cons /exp /=.
  have iterop_simplify: iterop 1 ZModE.( * ) sk0L one = sk0L.
  rewrite iterop1. smt(). rewrite iterop1. smt().


  have size_first: q = size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) .
  rewrite size_map size_range.
    smt(gt0_q). rewrite take_cat. rewrite size_first. rewrite -size_first.
    rewrite size_cat -size_first /=. rewrite (_ : q < q + 1) //.
    by smt(). simplify. rewrite take_cat -size_first. have q_not_lt_q: !(q < q) by smt().
    rewrite q_not_lt_q. simplify. rewrite cats0.
    have range_structure: range 1 (q + 1) = 1 :: (range 2 (q + 1)).  by smt(@List gt0_q).
    rewrite range_structure map_cons head_cons /exp /=. rewrite iterop1. smt(). 



    have take_simplify: 
         take q (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)) ++ [g ^ yL] ++
         [g ^ (sk0L * yL + (loge k'L - sk0L * yL) * if bL then zero else one)]) =
         take q (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))).
           rewrite take_cat.
           have :(q < size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)) ++ [g ^ yL])).
           rewrite size_cat. simplify.
           rewrite size_map size_range. smt(gt0_q). move => new_case. rewrite new_case. simplify.
           have size_gtuple_R : (size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) = q).
           rewrite size_map size_range.
           smt(gt0_q).
           rewrite take_size_cat. smt(). smt(@List).

           rewrite take_simplify. rewrite prodExCons.


  
    have take_q_gtuple : (take q (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))
                        = (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))).
    have size_gtuple_R : (size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) = q).
    rewrite size_map size_range.
    smt(gt0_q). smt(@List).

    rewrite take_q_gtuple.
    have size_eq : (size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) = size (nseq q zero)).
    rewrite size_nseq.
    rewrite size_map size_range.
    smt(gt0_q).
    have new_size_eq : (size (g ::  map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))
                      = size (one :: nseq q zero)).
    smt(gt0_q). rewrite /prodEx /ex.




  have prod_eq_head:
       prod (map (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) (zip (map (fun (i : int) => g ^ exp sk0L i)
       (range 1 (q + 1))) (one :: nseq (q - 1) zero))) =
      head witness (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))).
      pose gtuple_R := (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))).
      have gtuple_nonempty: 0 < size gtuple_R. smt(gt0_q @List).
      have gtuple_decomp: head witness gtuple_R :: behead gtuple_R = gtuple_R.
      apply head_behead.
      smt(). rewrite -gtuple_decomp. rewrite zip_cons.
      rewrite map_cons prod_cons.
      have first_term_simplify: 
      (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) (head witness gtuple_R, one) = (head witness gtuple_R) ^ one.
      rewrite /=.
      trivial. rewrite first_term_simplify.

    have head_exp_one: (head witness gtuple_R) ^ one = head witness gtuple_R. rewrite exp1. smt().
    rewrite head_exp_one.
    have second_term_e: prod (map (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) (zip (behead gtuple_R)
                        (nseq (q - 1) zero))) = e.
  

    have all_terms_e: forall pair, pair \in (zip (behead gtuple_R) (nseq (q - 1) zero)) =>
    (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) pair = e.  move=> pair pair_in. 
    simplify. have pair2_in: pair.`2 \in nseq (q - 1) zero.
    smt(@List).

    have exp_component_zero: pair.`2 = zero.
    smt(@List @ZModE gt0_q).
  

    rewrite /= exp_component_zero. rewrite exp0. smt().
    have all_elements_e: forall x, x \in (map (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) (zip (behead gtuple_R)
                         (nseq (q - 1) zero))) => x = e.
    move=> x x_in.
    rewrite mapP in x_in.
    case: x_in => pair [pair_in ->].
    apply all_terms_e.
    exact pair_in.
    have all_e_list: 
    map (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) (zip (behead gtuple_R) (nseq (q - 1) zero)) =
    map (fun _ => e) (zip (behead gtuple_R) (nseq (q - 1) zero)).  apply eq_in_map => pair pair_in.
    rewrite /=.
    apply all_elements_e. rewrite mapP.
    by exists pair. rewrite all_e_list.
    rewrite map_const. rewrite prod_nseq_unit.
    apply size_ge0. smt(). rewrite second_term_e. rewrite head_cons.  rewrite mulc1. smt().
    rewrite -mulc1 prod_eq_head. rewrite mulcC. smt(@G @GP).
              

    (* Simplify the take operation: when taking the first q elements from a concatenated list,
     we only get the first part (the mapped range), since the additional elements [g^yL] and 
     [g^(sk0L * yL + ...)] come after the first q elements *)
    have take_simplify: 
    take q (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)) ++ [g ^ yL] ++
    [g ^ (sk0L * yL + (loge k'L - sk0L * yL) * if bL then zero else one)]) =
      take q (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))). rewrite take_cat.
     have : ( q < size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)) ++ [g ^ yL])).
     rewrite size_cat. simplify. rewrite size_map size_range.

     smt(gt0_q). move => new_case. rewrite new_case.
     simplify.
     have size_gtuple_R : (size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) = q).
     rewrite size_map size_range.
     smt(gt0_q).
     rewrite take_size_cat. smt(). smt(@List).







      rewrite take_simplify. rewrite prodExConsGeneral.


      have take_q_gtuple : ( take q (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))
       = (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))).
      have size_gtuple_R : (size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) = q).
      rewrite size_map size_range.
      smt(gt0_q). smt(@List).

         rewrite take_q_gtuple.
         have size_eq : (size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))  = size( nseq q zero)).
         rewrite size_nseq.

         rewrite size_map size_range. smt(gt0_q).
         have new_size_eq :(size (g :: map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))
         = size (one :: nseq q zero)).
         smt(gt0_q).
         have g_one: g ^ one = g. smt(@G @GP). rewrite g_one. rewrite /prodEx. rewrite /ex.
         have zero_terms: prod (map (fun (i : group * GP.exp) => i.`1 ^ i.`2)
         (zip (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))(nseq q zero))) = e. 
         have all_zero: forall i, 0 <= i < (size (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))))
          => nth witness (nseq q zero) i = zero.
         move=> i i_bound.
        rewrite nth_nseq. 
        smt(gt0_q @List). smt().
        have all_terms_unit: 
            forall x, x \in (map (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2)
            (zip (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))
            (nseq q zero))) => x = e.
        move=> x0 x0_in. rewrite mapP in x0_in. case: x0_in => pair [pair_in x0_def]. rewrite x0_def.
        rewrite /=.
        have pair_snd_from_nseq: pair.`2 \in (nseq q zero).
        move: pair_in. smt(@List). rewrite mem_nseq in pair_snd_from_nseq.
        move: pair_snd_from_nseq => [q_pos pair_snd_eq].
        rewrite -pair_snd_eq. rewrite exp0. smt().
(* prove that whatever input is it will always return e*)
  have all_e_list: 
  map (fun (i0 : group * GP.exp) => i0.`1 ^ i0.`2) (zip (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)))
         (nseq q zero)) =
  map (fun _ => e) (zip (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))) (nseq q zero)).
  apply eq_in_map => pair pair_in. rewrite /=. apply all_terms_unit.
  rewrite mapP. by exists pair. rewrite all_e_list. rewrite map_const. rewrite prod_nseq_unit. apply size_ge0.
  smt(). rewrite zero_terms.
  rewrite mulc1. smt().



    pose gtuple_R := (map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1))).
    have size_gtuple_R: size gtuple_R = q. rewrite  /gtuple_R. rewrite size_map size_range.
           smt(gt0_q). smt(@List gt0_q).
           have :1 <= q by smt(gt0_q). move =>size_q. smt(@List). smt(@List gt0_q). smt(@List gt0_q).
        have :1 <= q by smt(gt0_q). move =>size_q. smt(@List).
    
    pose gtuple_R := map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)).
    have size_gtuple_R : size gtuple_R = q by smt(@G @List @GP).
   
    have nth_simplify:
  
     nth witness
    (gtuple_R ++ [g ^ yL] ++
     [g ^ (sk0L * yL + (loge k'L - sk0L * yL) * if bL then zero else one)]) (q + 1) =
      g ^ (sk0L * yL + (loge k'L - sk0L * yL) * if bL then zero else one).
    rewrite nth_cat.
    rewrite size_cat size_gtuple_R /=. smt().
    rewrite nth_simplify.
    case bL. rewrite /=.
  
    
    have zero_term: (loge k'L - sk0L * yL) * zero = zero by ring.
    rewrite zero_term. have add_zero: sk0L * yL + zero = sk0L * yL by ring.
    rewrite add_zero. rewrite -expM. smt(). rewrite /=.
    have one_term: (loge k'L - sk0L * yL) * one = (loge k'L - sk0L * yL) by ring.
    rewrite one_term.
    have add_simplify: sk0L * yL + (loge k'L - sk0L * yL) = loge k'L by ring.
    rewrite add_simplify. rewrite expgK. smt().

    pose gtuple_R := map (fun (i : int) => g ^ exp sk0L i) (range 1 (q + 1)).
    have size_gtuple_R: size gtuple_R = q. smt(@List @G).
    
    rewrite nth_cat. have size_concat: size (gtuple_R ++ [g ^ yL]) = q + 1.
    rewrite size_cat size_gtuple_R. smt().
    rewrite size_concat. have gt : q < q + 1 by smt(). rewrite gt. simplify.
    rewrite nth_cat size_gtuple_R. simplify. smt(). smt().

 qed.












end Security.





