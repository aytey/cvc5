(set-logic QF_NIA)
(set-info :status sat)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun c () Int)
(declare-fun d () Int)
(declare-fun e () Int)
(assert (or (<= (+ 40 a) 0) (>= d (+ c (* a b e) (* (- 1) c)) 0)))
(check-sat)
