(set-logic QF_NOLL)

(declare-sort Sll_t 0)

(declare-fun f () (Field Sll_t Sll_t))

(define-fun lso ((?in Sll_t) (?out Sll_t)) Space
(tospace 
(exists ((?u Sll_t))
(tobool
(ssep (pto ?in (ref f ?u)) (zplus (lso ?u ?out)))
))))

(declare-fun nil () Sll_t)

(declare-fun x_emp () Sll_t)
(declare-fun y_emp () Sll_t)
(declare-fun z_emp () Sll_t)
(declare-fun alpha1 () SetLoc)
(assert
    (tobool (ssep (pto x_emp (ref f y_emp)) (pto y_emp (ref f z_emp))))
)
(assert
  (not
    (tobool (index alpha1 (lso x_emp z_emp)))
))

(check-sat)
