
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
(declare-fun Y () Bst_t)
(declare-fun M1 () BagInt)
(declare-fun M2 () BagInt)
(declare-fun M3 () BagInt)
(declare-fun M4 () BagInt)
(declare-fun M5 () BagInt)
(declare-fun M6 () BagInt)
(declare-fun key () Int)
(declare-fun d () Int)

;; declare set of locations

(declare-fun alpha1 () SetLoc)
(declare-fun alpha2 () SetLoc)
(declare-fun alpha3 () SetLoc)
(declare-fun alpha4 () SetLoc)
(declare-fun alpha5 () SetLoc)

Entl: bsthole(root,cur1,M1,M2) * cur1 |->((left,cur2), (right,Y)) *  bst(cur2, M5) * bst(Y, M6) & 
M3 = {cur1.data} cup M5 cup M6 & M5 < cur1.data < M6 & cur1 != nil & (key in M0 => M1 = M0) & ((! key in M0) => M1 = M0 cup {key}) & ( key in M3 => M2 = M3 ) & ( (! key in M3) => M2 = M3 cup {key}) &  
cur1.data > key & cur2 != nil & M2 = {cur1.data} cup M4 cup M6 |- 
bsthole(root,cur2,M1,M4) * bst(cur2,M5) & cur2 != nil & (key in M0 => M1 = M0) & ((! key in M0) => M1 = M0 cup {key}) & ( key in M5 => M4 = M5 ) & ( (! key in M5) => M4 = M5 cup {key})

(assert 
	(and
	(tobool 
	(ssep 
		(index alpha1 (bsthole root cur1 M1 M2) )
		(pto cur1 (sref (ref left cur2) (ref right Y) (data d) ) ) 
		(index alpha2 (bst cur2 M5) )
		(index alpha3 (bst Y M6) )
	))
	(= M3 (bag-union (singleton d) (bag-union M5 M6)) )
	(bag-lt M5 (singleton d) )
	(bag-lt (singleton d) M6)
	(distinct cur1 nil)
	(ite (bag-sub (singleton key) M0) (= M1 M0) (= M1 (bag-union M0 (singleton key)) ) ) 
	(ite (bag-sub (singleton key) M3) (= M2 M3) (= M2 (bag-union M3 (singleton key)) ) ) 
	(> d key) (distinct cur2 nil)
	(= M2 (bag-union (singleton d) (bag-union M4 M6) ) )
	)
)

(assert (not 
	(and 
	(tobool 
		(ssep 
		(index alpha4 (bsthole root cur2 M1 M4 )) 
		(index alpha5 (bst cur2 M5))
		)
	)
	(distinct cur2 nil)
	(ite (bag-sub (singleton key) M0) (= M1 M0) (= M1 (bag-union M0 (singleton key)) ) ) 
	(ite (bag-sub (singleton key) M5) (= M4 M5) (= M4 (bag-union M5 (singleton key)) ) ) 
	)
))

(check-sat)
