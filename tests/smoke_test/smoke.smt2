(set-logic QF_LRA)

(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)

(assert (<= (+ x1 x2) 5))
(assert (<= (+ x2 x3) 10))
(assert (<= (+ x3 x4) 15))
(assert (<= (+ x4 x5) 20))
(assert (>= x1 0.0))
(assert (<= x5 10.0))

(check-sat)
(exit)