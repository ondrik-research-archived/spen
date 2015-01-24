
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
(declare-fun cur1 () Bst_t)
(declare-fun cur2 () Bst_t)
(declare-fun parent1 () Bst_t)
(declare-fun parent2 () Bst_t)
(declare-fun rt () Bst_t)
(declare-fun X () Bst_t)
(declare-fun Y () Bst_t)
(declare-fun Z () Bst_t)
(declare-fun M0 () BagInt)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M33 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)
(declare-fun M6 () BagInt)
(declare-fun M7 () BagInt)
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
(declare-fun alpha6 () SetLoc)
(declare-fun alpha7 () SetLoc)
(declare-fun alpha8 () SetLoc)
(declare-fun alpha9 () SetLoc)

;; VC: root |-> ((left, X), (right, rt)) * bst(X, M1) * bsthole(rt, parent1, M2, M3) * 
;; parent1 |-> ((left, cur1), (right, Y)) * cur1 |-> ((left, cur2), (right, Z)) * bst(cur2, M6) * bst(Z,M7) * 
;; bst(Y, M5) & M2 = M0 \ ({key} cup M1 cup {keymin}) & M1 < root.data <  M2 cup {keymin} & 
;; M3 = ({parent1.data} cup M4 cup M5) \ {keymin} & M4 = {cur1.data} cup M6 cup M7 & M4 < parent1.data < M5 & 
;; M33 = ({cur1.data} cup M6 cup M7) \ {keymin} & M6 < cur1.data < M7 & keymin in M4 & keymin <= M4 & keymin <= M2 & 
;; ! parent1  = nil & ! cur1 = nil & parent2 = cur1 & ! cur2 =nil & key = root.data |- 
;; root |-> ((left, X), (right, rt)) * bst(X, M1) * bsthole(rt, parent2, M2, M33) * parent2 |-> ((left, cur2), (right, Z)) *
;; bst(cur2, M6) * bst(Z, M7) & M2 = M0 \ ({key} cup M1 cup {keymin}) & M1 < root.data <  M2 cup {keymin} & 
;; M33 = ({parent2.data} cup M6 cup M7) \ {keymin} & M6 < parent2.data < M7 & keymin in M6 & keymin <= M6 & 
;; keymin <= M2 & ! parent2  = nil & ! cur2 = nil & key = root.data

(assert 
	(and
	(tobool 
	(ssep 
		(pto root (sref (ref left X) (ref right rt) (data key) ) ) 
		(index alpha1 (bst X M1) )
		(index alpha2 (bsthole rt parent1 M2 M3) )
		(pto parent1 (sref (ref left cur1) (ref right Y) (data d2) ) ) 
		(pto cur1 (sref (ref left cur2) (ref right Z) (data d3) ) ) 
		(index alpha3 (bst cur2 M6) )
		(index alpha4 (bst Z M7) )
		(index alpha5 (bst Y M5) )
	))
	(= M2 (bag-diff M0 (bag-union (singleton key) (bag-union M1 (singleton keymin)) ) ) )
	(bag-lt M1 (singleton key) )
	(bag-lt (singleton key) (bag-union M2 (singleton keymin) ) )
	(= M3 (bag-diff (bag-union (singleton d2) (bag-union M4 M5) ) (singleton keymin) ) )
	(= M4 (bag-union (singleton d3) (bag-union M6 M7) ) )
	(bag-lt M4 (singleton d2) )
	(bag-lt (singleton d2) M5 )
	(= M33 (bag-diff (bag-union (singleton d3) (bag-union M6 M7) ) (singleton keymin) ) )
	(bag-lt M6 (singleton d3) )
	(bag-lt (singleton d3) M7 )
	(bag-sub (singleton keymin) M4)
	(bag-le (singleton keymin) M4)
	(bag-le (singleton keymin) M2)
	(distinct parent1 nil)
	(distinct cur1 nil)
	(= parent2 cur1)
	(distinct cur2 nil)
	)
)

;; root |-> ((left, X), (right, rt)) * bst(X, M1) * bsthole(rt, parent2, M2, M33) * parent2 |-> ((left, cur2), (right, Z)) *
;; bst(cur2, M6) * bst(Z, M7) & M2 = M0 \ ({key} cup M1 cup {keymin}) & M1 < root.data <  M2 cup {keymin} & 
;; M33 = ({parent2.data} cup M6 cup M7) \ {keymin} & M6 < parent2.data < M7 & keymin in M6 & keymin <= M6 & 
;; keymin <= M2 & ! parent2  = nil & ! cur2 = nil & key = root.data

(assert (not 
	(and
	(tobool 
	(ssep 
		(pto root (sref (ref left X) (ref right rt) (data key) ) ) 
		(index alpha6 (bst X M1) )
		(index alpha7 (bsthole rt parent2 M2 M33) )
		(pto parent2 (sref (ref left cur2) (ref right Z) (data d3) ) ) 
		(index alpha8 (bst cur2 M6) )
		(index alpha9 (bst Z M7) )
	))
	(= M2 (bag-diff M0 (bag-union (singleton key) (bag-union M1 (singleton keymin)) ) ) )
	(bag-lt M1 (singleton key) )
	(bag-lt (singleton key) (bag-union M2 (singleton keymin) ) )
	(= M33 (bag-diff (bag-union (singleton d3) (bag-union M6 M7) ) (singleton keymin) ) )
	(bag-lt M6 (singleton d3) )
	(bag-lt (singleton d3) M7 )
	(bag-sub (singleton keymin) M6)
	(bag-le (singleton keymin) M6)
	(bag-le (singleton keymin) M2)
	(distinct parent2 nil)
	(distinct cur2 nil)
	)
))

(check-sat)
