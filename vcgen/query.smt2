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
(declare-const pv (Array Int Int))
(declare-const px (Array Int Int))
(declare-const ps Set)
(declare-const qid (Array Int Int))
(declare-const qs Set)
(declare-const y (Array Int Int))
(declare-const pc!qs (Array Int Int))
(assert (not (and (forall ((A Int)
                           (r Set)
                           (pv (Array Int Int)))
                          true)
                  (forall ((A Int)
                           (r Set)
                           (pv (Array Int Int)))
                          (and (=> (forall ((B Int))
                                           (and (set_mem B qs)
                                                (= (select pc!qs B) 0)))
                                   (forall ((B Int))
                                           (and (=> (and (set_mem B qs)
                                                         (= (select pc!qs B) 1))
                                                    (forall ((C Int)
                                                             (_ Set))
                                                            true))
                                                (=> (and (set_mem B qs)
                                                         (= (select pc!qs B) 2))
                                                    (forall ((C Int)
                                                             (_ Set))
                                                            true)))))
                               (forall ((B!0 Int)
                                        (pc!qs (Array Int Int))
                                        (pcNext!qs (Array Int Int))
                                        (C Int)
                                        (_ Set)
                                        (qid (Array Int Int))
                                        (y (Array Int Int))
                                        (px (Array Int Int))
                                        (B Int)
                                        (C Int))
                                       (=> (set_mem B!0 qs)
                                           (and (=> (and (forall ((B Int))
                                                                 (and (=> (and (set_mem B qs)
                                                                               (= (select pc!qs B) 1))
                                                                          (forall ((C Int)
                                                                                   (_ Set))
                                                                                  true))
                                                                      (=> (and (set_mem B qs)
                                                                               (= (select pc!qs B) 2))
                                                                          (forall ((C Int)
                                                                                   (_ Set))
                                                                                  true))))
                                                         (and (= (select pc!qs B) 1)
                                                              (= pcNext!qs (store pc!qs B 2)))
                                                         (set_mem B!0 qs))
                                                    (forall ((B Int))
                                                            (and (=> (and (set_mem B qs)
                                                                          (= (select pcNext!qs B) 1))
                                                                     (forall ((C Int)
                                                                              (_ Set))
                                                                             true))
                                                                 (=> (and (set_mem B qs)
                                                                          (= (select pcNext!qs B) 2))
                                                                     (forall ((C Int)
                                                                              (_ Set))
                                                                             true)))))
                                                (=> (and (forall ((B Int))
                                                                 (and (=> (and (set_mem B qs)
                                                                               (= (select pc!qs B) 1))
                                                                          (forall ((C Int)
                                                                                   (_ Set))
                                                                                  true))
                                                                      (=> (and (set_mem B qs)
                                                                               (= (select pc!qs B) 2))
                                                                          (forall ((C Int)
                                                                                   (_ Set))
                                                                                  true))))
                                                         (and (= (select pc!qs B) 2)
                                                              (or
                                                               (= pcNext!qs (store pc!qs B 1))
                                                               (= pcNext!qs (store pc!qs B 3))))
                                                         (set_mem B!0 qs))
                                                    (forall ((B Int))
                                                            (and (=> (and (set_mem B qs)
                                                                          (= (select pcNext!qs B) 1))
                                                                     (forall ((C Int)
                                                                              (_ Set))
                                                                             true))
                                                                 (=> (and (set_mem B qs)
                                                                          (= (select pcNext!qs B) 2))
                                                                     (forall ((C Int)
                                                                              (_ Set))
                                                                             true))))))))
                               (forall ((pc!qs (Array Int Int))
                                        (pcNext!qs (Array Int Int))
                                        (C Int)
                                        (_ Set)
                                        (qid (Array Int Int))
                                        (y (Array Int Int))
                                        (px (Array Int Int)))
                                       (=> (and (forall ((B Int))
                                                        (and (set_mem B qs)
                                                             (= (select pc!qs B) 3)))
                                                (forall ((B Int))
                                                        (and (=> (and (set_mem B qs)
                                                                      (= (select pc!qs B) 1))
                                                                 (forall ((C Int)
                                                                          (_ Set))
                                                                         true))
                                                             (=> (and (set_mem B qs)
                                                                      (= (select pc!qs B) 2))
                                                                 (forall ((C Int)
                                                                          (_ Set))
                                                                         true)))))
                                           (forall ((i Int))
                                                   (=> (set_mem i qs)
                                                       (= (select y i) 1))))))))))
(check-sat)