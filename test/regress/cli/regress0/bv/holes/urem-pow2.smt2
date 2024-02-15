; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
	(bvurem x #b01000)
	(concat #b00 ((_ extract 2 0) x)))))
(check-sat)
(exit)
