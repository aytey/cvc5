; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x1 (_ BitVec 4))
(declare-const x2 (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (not (=
	(bvmul (bvadd x1 x2) y)
	(bvadd (bvmul x1 y) (bvmul x2 y)))))
(check-sat)
(exit)
