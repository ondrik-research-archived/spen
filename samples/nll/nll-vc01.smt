(set-logic QF_NOLL)

(declare-sort NLL_lvl1_t 0)
(declare-sort NLL_lvl2_t 0)

; 'next' selector of level 1
(declare-fun next1 () (Field NLL_lvl1_t NLL_lvl1_t))
; 'next' selector of level 2
(declare-fun next2 () (Field NLL_lvl2_t NLL_lvl2_t))
; the bridge from level 2 to level 1
(declare-fun down () (Field NLL_lvl2_t NLL_lvl1_t))

; singly-linked list
(define-fun lso ((?in NLL_lvl1_t) (?out NLL_lvl1_t))
  Space (tospace (or (= ?in ?out) 
    (exists ((?u NLL_lvl1_t)) (tobool (ssep
      (pto ?in (ref next1 ?u))
      (lso ?u ?out))
)))))

; singly-linked list of singly-linked lists
(define-fun nll ((?in NLL_lvl2_t) (?out NLL_lvl2_t) (?boundary NLL_lvl1_t)
  Space (tospace (or (= ?in ?out)
    (exists ((?u NLL_lvl2_t) (?Z1 NLL_lvl1_t)) (tobool (ssep
      (pto ?in (sref
        (ref next2 ?u)
        (ref down ?Z1)))
      (lso ?Z1 ?boundary)
      (nll ?u ?out))
)))))

(declare-fun first () NLL_lvl2_t)
(declare-fun last () NLL_lvl2_t)
(declare-fun x1 () NLL_lvl1_t)
(declare-fun x2 () NLL_lvl1_t)
(declare-fun x3 () NLL_lvl1_t)
(declare-fun x4 () NLL_lvl1_t)
(declare-fun x5 () NLL_lvl1_t)
(declare-fun nil_lvl1 () NLL_lvl1_t)
(declare-fun nil_lvl2 () NLL_lvl2_t)

(declare-fun alpha1 () SetLoc)

(assert (tobool (ssep
  (pto first (sref
    (ref next2 last)
    (ref down x1)))
  (pto x1 (ref next1 x4))
  (pto x4 (ref next1 x5))
  (pto x5 (ref next1 nil_lvl1))
  (pto last (sref
    (ref next2 nil_lvl2)
    (ref down x2)))
  (pto x2 (ref next1 x3))
  (pto x3 (ref next1 nil_lvl1))
)))

(assert (not (tobool (index alpha1
  (nll first last nil_lvl1)
))))

(check-sat)

