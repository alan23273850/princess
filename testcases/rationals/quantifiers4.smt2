(set-logic LRA)

(declare-fun x () Real)
(assert (forall ((y Real)) (=> (> y 0) (>= y x))))
(check-sat)
(set-option :regular-output-channel "/dev/null")
(get-model)
(get-value (x (+ x 10)))
(exit)