; Generated SMT2 for partial-4-tree sparse graph formulas
(set-logic QF_NRA)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Real)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)

; formula 1: vars [2, 3, 1]
(assert (>= (+ (* 4 x_2) (* 10 x_3) (* (* 7 x_2) x_2) (* (* -8 x_3) x_3) (* (* 2 x_2) x_3) (* (* 7 x_3) x_1)) 0))

; formula 2: vars [2, 3, 5]
(assert (>= (+ (* -3 x_2) (* (* 7 x_5) x_5) (* (* -5 x_2) x_3) (* (* -1 x_3) x_5)) 0))

; formula 3: vars [2, 4, 5]
(assert (>= (+ (* -10 x_4) (* 6 x_5) (* (* 7 x_2) x_2) (* (* 3 x_4) x_4) (* (* 4 x_5) x_5)) 0))

; formula 4: vars [6, 1]
(assert (>= (+ (* 4 x_6) (* (* 2 x_1) x_1) (* (* -1 x_6) x_1)) 0))

; formula 5: vars [7, 4]
(assert (>= (+ (* -10 x_4) (* (* 9 x_7) x_4)) 0))

(check-sat)
(exit)
