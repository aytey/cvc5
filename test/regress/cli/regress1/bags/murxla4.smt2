(set-logic ALL)
(set-info :status sat)
(declare-const x Int)
(assert ((_ divisible 2) (bag.count 0.0 (bag 0.0 x))))
(check-sat)
