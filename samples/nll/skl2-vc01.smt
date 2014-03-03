(set-logic QF_NOLL)

(declare-sort SL2_t 0)

(declare-fun n1 () (Field SL2_t SL2_t))
(declare-fun n2 () (Field SL2_t SL2_t))

; one-level skip list (i.e. a SLL)
(define-fun skl1 ((?hd SL2_t) (?ex SL2_t) (?border SL2_t)) Space
  (tospace (or (= ?hd ?ex)
  (exists ((?tl SL2_t))
  (tobool (ssep
    (pto ?hd (sref (ref n2 ?border) (ref n1 ?tl)))
    (skl1 ?tl ?ex ?border))
)))))

; two-level skip list
(define-fun skl2 ((?hd SL2_t) (?ex SL2_t) (?border SL2_t)) Space
  (tospace (or (= ?hd ?ex)
  (exists ((?tl SL2_t) (?Z1 SL2_t))
  (tobool (ssep
    (pto ?hd (sref (ref n2 ?tl) (ref n1 ?Z1)))
    (skl1 ?Z1 ?tl ?border)
    (skl2 ?tl ?ex ?border))
)))))

(declare-fun head () SL2_t)
(declare-fun tail () SL2_t)

(declare-fun alpha1 () SetLoc)

(assert (tobool (ssep
  (pto head (sref (ref n2 tail) (ref n1 tail)))
  (pto tail (sref (ref n2 nil) (ref n1 nil)))
)

(assert (not
  (tobool (index alpha1 (skl2 head tail nil)))
))

; check whether the negation of the entailment is satisfiable
(check-sat)
