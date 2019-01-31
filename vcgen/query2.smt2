(define-sort Elt () Int)
(define-sort Set () (Array Elt Bool))
(define-sort IntMap () (Array Elt Elt))
(define-fun set_emp () Set ((as const Set) false))
(define-fun set_mem ((x Elt) (s Set)) Bool (select s x))
(define-fun set_add ((s Set) (x Elt)) Set  (store s x true))
(define-fun set_cap ((s1 Set) (s2 Set)) Set ((_ map and) s1 s2))
(define-fun set_cup ((s1 Set) (s2 Set)) Set ((_ map or) s1 s2))
(define-fun set_com ((s Set)) Set ((_ map not) s))
(define-fun set_dif ((s1 Set) (s2 Set)) Set (set_cap s1 (set_com s2)))
(define-fun set_sub ((s1 Set) (s2 Set)) Bool (= set_emp (set_dif s1 s2)))
(define-fun set_minus ((s1 Set) (x Elt)) Set (set_dif s1 (set_add set_emp x)))
(declare-fun set_size (Set) Int)
(declare-const l (Array Int Int))
(declare-const resID (Array Int Int))
(declare-const term (Array Int Int))
(declare-const id (Array Int Int))
(declare-const myVote (Array Int Int))
(declare-const vote (Array Int Int))
(declare-const k (Array Int Int))
(declare-const fs Set)
(declare-const count (Array Int Int))
(declare-const cs Set)
(declare-const f0 Int)
(declare-const t (Array Int Int))
(declare-const voted (Array Int Int))
(declare-const myTerm (Array Int Int))
(declare-const votedFor (Array Int Int))
(declare-const votes (Array Int (Array Int Int)))
(declare-const isLeader (Array Int Int))
(declare-const pc!fs (Array Int Int))
(assert (not (and true
                  
                  (forall ((A Int)
                           (r Set)
                           (voted (Array Int Int)))
                          (=> true
                              (and true
                                   
                                   (forall ((B Int)
                                            (r Set)
                                            (isLeader (Array Int Int))
                                            (count (Array Int Int)))
                                           (=> true
                                               (and 
                                                    (forall ((A0 Int)
                                                             (pc!fs (Array Int Int))
                                                             (pcNext!fs (Array Int Int))
                                                             (C Int)
                                                             (myVote (Array Int Int))
                                                             (id (Array Int Int))
                                                             (resID (Array Int Int))
                                                             (t (Array Int Int))
                                                             (myTerm (Array Int Int))
                                                             (voted (Array Int Int))
                                                             (votedFor (Array Int Int))
                                                             (votes (Array Int (Array Int Int)))
                                                             (vote (Array Int Int))
                                                             (count (Array Int Int))
                                                             (l (Array Int Int))
                                                             (k (Array Int Int))
                                                             (B Int)
                                                             (isLeader (Array Int Int))
                                                             (A Int)
                                                             (B Int)
                                                             (C Int))
                                                            (=> (and (set_mem A0 fs) (= (select pc!fs A) 1))
                                                                (and (=> (and (forall ((A Int))
                                                                                      (and (=> (and (set_mem A fs)
                                                                                                    (= (select pc!fs A) 1))
                                                                                               (or
                                                                                                (and (and true
                                                                                                          (forall ((i Int))
                                                                                                                  (=> (set_mem i cs)
                                                                                                                      (and (<= (+ (select k i) (select l i)) (set_size fs))
                                                                                                                           (= (select count i) (select l i)))))
                                                                                                          true)
                                                                                                     true)))
                                                                                           ))
                                                                              (and (= (select pc!fs A) 1)
                                                                                   (or
                                                                                    (= pcNext!fs (store pc!fs A 1))
                                                                                    ))
                                                                              (set_mem A0 fs))
                                                                         (and 
                                                                              (=> (not (> (select (store (store t A (select (store id C C) C)) A (select term C)) A0) (select myTerm A0)))
                                                                                  (and (=> (and (<= (select myTerm A0) (select (store (store t A (select (store id C C) C)) A (select term C)) A0))
                                                                                                (or
                                                                                                 (= (select voted A0) 0)
                                                                                                 (= (select votedFor A0) (select (store (store resID A (select (store id C C) C)) A (select term C)) A0))))
                                                                                           (and (=> (= (select (store vote C (select (store (store myVote A 0) A 1) A)) C) 1)
                                                                                                    (and 
                                                                                                         (=> (not (and (and (= (select (store vote C (select (store (store myVote A 0) A 1) A)) C) 1)
                                                                                                                            (= (select (store votedFor A (select (store (store resID A (select (store id C C) C)) A (select term C)) A0)) A0) C))
                                                                                                                       (= (select term C) (select myTerm A0))))
                                                                                                             (forall ((A Int))
                                                                                                                     (and 
                                                                                                                          (=> (and (set_mem A fs)
                                                                                                                                   (= (select pcNext!fs A) 2))
                                                                                                                              (or
                                                                                                                               (and (and true
                                                                                                                                         (forall ((i Int))
                                                                                                                                                 (=> (set_mem i cs)
                                                                                                                                                     (and (<= (+ (select k i) (select l i)) (set_size fs))
                                                                                                                                                          (= (select (store count C (+ (select count C) 1)) i) (select l i)))))
                                                                                                                                         true)
                                                                                                                                    true)
                                                                                                                               (and (and true
                                                                                                                                         (forall ((i Int))
                                                                                                                                                 (=> (and (set_mem i cs)
                                                                                                                                                          (= (select isLeader i) 1))
                                                                                                                                                     (< (set_size fs) (* (select (store count C (+ (select count C) 1)) i) 2))))
                                                                                                                                         (forall ((i Int)
                                                                                                                                                  (j Int))
                                                                                                                                                 (=> (and (set_mem i cs)
                                                                                                                                                          (set_mem j cs)
                                                                                                                                                          (> (select (store count C (+ (select count C) 1)) i) (/ (set_size fs) 2))
                                                                                                                                                          (> (select (store count C (+ (select count C) 1)) j) (/ (set_size fs) 2))
                                                                                                                                                          (= (select term i) (select term j))
                                                                                                                                                          (= (select isLeader j) 1)
                                                                                                                                                          (= (select isLeader i) 1))
                                                                                                                                                     (= i j)))
                                                                                                                                         true)
                                                                                                                                    true))))))))
                                                                                                ))
                                                                                       ))))
                                                                     )))
                                                    )))))))))
(check-sat)
