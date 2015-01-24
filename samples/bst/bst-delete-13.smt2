
; Extending QF_S:
; constant emptybag, 
; the function singleton, 
; the multiset comparison operator bag-lt, bag-le, bag-gt, bag-ge
; bag-union, bag-diff, bag-sub

(set-logic QF_S)

;; declare sorts
(declare-sort Bst_t 0)

;; declare fields
(declare-fun left () (Field Bst_t Bst_t))
(declare-fun right () (Field Bst_t Bst_t))
(declare-fun data () (Field Bst_t Int))

;; declare predicates

;; bst(E,M)::= E = nil & emp & M = emptybag | 
;; exists X,Y,M1,M2. E |-> ((left,X), (right,Y)) * bst(X,M1) * bst(Y,M2) & M = {E.data} cup M1 cup M2 & M1 < E.data < M2


(define-fun bst ((?E Bst_t) (?M BagInt)) Space (tospace 
	(or 
	(and (= ?E nil) 
		(tobool emp
		)
		(= ?M emptybag)
	)
 
	(exists ( (?X Bst_t) (?Y Bst_t) (?M1 BagInt) (?M2 BagInt) (?d Int) ) 
	(and (distinct ?E nil) 
		(tobool (ssep 
		(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d)) ) 
		(bst ?X ?M1)
		(bst ?Y ?M2)
		)
		)
		(= ?M (bag-union (singleton ?d) (bag-union ?M1 ?M2) ) )
		(bag-lt ?M1 (singleton ?d))
		(bag-lt (singleton ?d) ?M2)
	)
	)
	)
))

;; bsthole(E,F,M1,M2)::= E = F & emp & M1 = M2 | 
;; exists X,Y,M3,M4. E |-> ((left,X), (right,Y)) * bst(X,M3) * bsthole(Y,F,M4,M2) & M1={E.data} cup M3 cup M4 & M3 < E.data < M4 |
;; exists X,Y,M3,M4. E |-> ((left,X), (right,Y)) * bsthole(X,F,M3,M2) * bst(Y,M4) & M1={E.data} cup M3 cup M4 & M3 < E.data < M4

(define-fun bsthole ((?E Bst_t) (?F Bst_t) (?M1 BagInt) (?M2 BagInt)) Space (tospace 
	(or 
	(and (= ?E ?F) 
		(tobool emp
		)
		(= ?M1 ?M2)
	)
 
	(exists ((?X Bst_t) (?Y Bst_t) (?M3 BagInt) (?M4 BagInt) (?d Int)) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
		(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d)) ) 
		(bst ?X ?M3)
		(bsthole ?Y ?F ?M4 ?M2)
		)
		)
		(= ?M1  (bag-union (singleton ?d) (bag-union ?M3 ?M4) ) )
		(bag-lt ?M3 (singleton ?d) )
		(bag-lt (singleton ?d) ?M4 )
	) 
	)

	(exists ((?X Bst_t) (?Y Bst_t) (?M3 BagInt) (?M4 BagInt) (?d Int)) 
	(and (distinct ?E ?F) 
		(tobool (ssep 
		(pto ?E (sref (ref left ?X) (ref right ?Y) (ref data ?d)) ) 
		(bsthole ?X ?F ?M3 ?M2)
		(bst ?Y ?M4)
		)
		)
		(= ?M1 (bag-union (singleton ?d) (bag-union ?M3 ?M4) ) )
		(bag-lt ?M3 (singleton ?d) )
		(bag-lt (singleton ?d) ?M4 )
	) 
	)
	)
))

;; declare variables
(declare-fun root () Bst_t)
(declare-fun cur () Bst_t)
(declare-fun parent () Bst_t)
(declare-fun rt () Bst_t)
(declare-fun X () Bst_t)
(declare-fun Y () Bst_t)
(declare-fun Z () Bst_t)
(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)
(declare-fun M6 () BagInt)
(declare-fun key () Int)
(declare-fun keymin () Int)
(declare-fun d2 () Int)
(declare-fun d3 () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)

;; VC: bst(X, M1) * bsthole(rt, parent, M2, M3) * parent |-> ((left, Z), (right, Y)) * cur |-> ((left,X), (right,rt)) * bst(Z, M6)
;;  * bst(Y, M5) & M2 = M0 \ ({key} cup M1 cup {keymin}) & M4 = {cur.data} cup M6 & M1 < root.data <  M2 cup {keymin} & 
;; M3 = ({parent.data} cup M4 cup M5) \ {keymin} & M4 < parent.data < M5 & cur.data < M6 & keymin in M4 & keymin <= M4 & 
;; keymin <= M2 & ! parent  = nil & ! cur = nil & key = root.data |-
;; bst(cur, M1) & M1 = M0 \ {key}

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bst X M1) )
		(index alpha2 (bsthole rt parent M2 M3) )
		(pto parent (sref (ref left Z) (ref right Y) (data d2) ) ) 
		(pto cur (sref (ref left X) (ref right rt) (data d3) ) ) 
		(index alpha3 (bst Z M6) )
		(index alpha4 (bst Y M5) )
	))
	(= M2 (bag-diff M0 (bag-union (singleton key) (bag-union M1 (singleton keymin)) ) ) )
	(= M4 (bag-union (singleton d3) M6 ) )
	(bag-lt M1 (singleton key) )
	(bag-lt (singleton key) (bag-union M2 (singleton keymin) ) )
	(= M3 (bag-diff (bag-union (singleton d2) (bag-union M4 M5) ) (singleton keymin) ) )
	(bag-lt M4 (singleton d2) )
	(bag-lt (singleton d2) M5 )
	(bag-lt (singleton d3) M6 )
	(bag-sub (singleton keymin) M4)
	(bag-le (singleton keymin) M4)
	(bag-le (singleton keymin) M2)
	(distinct parent nil)
	(distinct cur nil)
	)
)

;; bst(cur, M1) & M1 = M0 \ {key}

(assert (not 
	(and
	(tobool 
	(ssep 
		(index alpha5 (bst cur M1) )
	))
	(= M1 (bag-diff M0 (singleton key)) )
	)
))

(check-sat)
