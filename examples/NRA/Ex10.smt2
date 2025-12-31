(set-logic QF_NRA)
(declare-fun x_1 () Real)
(declare-fun x_2 () Real)
(declare-fun x_3 () Real)
(declare-fun x_4 () Real)
(declare-fun x_5 () Real)
(declare-fun x_6 () Real)
(declare-fun x_7 () Real)
(declare-fun x_8 () Real)

; formula 1: vars [3, 1, 2]
(assert (>= (+ (* (* 10 x_1) x_1) (* (* (* (* 10 x_3) x_1) x_1) x_2) (* (* (* (* 8 x_1) x_1) x_1) x_1) (* (* (* -7 x_1) x_2) x_2) (* (* 10 x_2) x_2) (* (* (* 8 x_1) x_1) x_2)) 0))

; formula 2: vars [3, 4, 5]
(assert (>= (+ (* (* (* (* 0 x_4) x_4) x_5) x_5) (* (* (* (* 10 x_4) x_4) x_4) x_4) (* (* (* 4 x_3) x_5) x_5) (* (* (* 0 x_3) x_4) x_5) (* (* (* (* 5 x_3) x_4) x_4) x_4) (* (* (* 2 x_5) x_5) x_5)) 0))

; formula 3: vars [3, 4, 7]
(assert (>= (+ (* 4 x_3) (* (* (* -4 x_3) x_3) x_4) (* (* 4 x_3) x_7) (* 8 x_7) (* (* (* -9 x_4) x_4) x_4) (* (* (* (* 5 x_3) x_4) x_4) x_7)) 0))

; formula 4: vars [6, 4, 5]
(assert (>= (+ (* (* (* (* 2 x_6) x_4) x_5) x_5) (* (* (* 4 x_4) x_4) x_4) (* (* 7 x_6) x_4) (* (* (* 3 x_4) x_4) x_5) (* (* (* (* 2 x_6) x_4) x_4) x_4) (* -10 x_5)) 0))

; formula 5: vars [8, 4]
(assert (>= (+ (* (* (* -9 x_4) x_4) x_4) (* (* 3 x_8) x_8) (* (* (* (* 10 x_8) x_8) x_8) x_4) (* (* (* -3 x_8) x_8) x_4)) 0))

(check-sat)
(exit)
