; EXPECT: unsat
(set-logic QF_UFLIA)
(set-info :smt-lib-version 2.6)
(set-info :source |
  SMT2 problem corresponding to a linear arithmetic proof step in the proof generated by the veriT solver for the SMT-LIB problem
  QF_UFLIA/wisas/xs_12_22.smt2
|)
(set-info :status unsat)
(declare-fun arg0 () Int)
(declare-fun arg1 () Int)
(declare-fun fmt0 () Int)
(declare-fun fmt1 () Int)
(declare-fun distance () Int)
(declare-fun fmt_length () Int)
(declare-fun adr_lo () Int)
(declare-fun adr_medlo () Int)
(declare-fun adr_medhi () Int)
(declare-fun adr_hi () Int)
(declare-fun format (Int) Int)
(declare-fun percent () Int)
(declare-fun s () Int)
(declare-fun s_count (Int) Int)
(declare-fun x () Int)
(declare-fun x_count (Int) Int)
(assert (not (! (not (! (<= fmt0 arg1) :named p_1)) :named p_0)))
(assert (not (! (<= (! (+ 1 (! (x_count 0) :named p_4)) :named p_3) arg1) :named p_2)))
(assert (not (! (not (! (= distance 22) :named p_6)) :named p_5)))
(assert (not (! (not (! (= arg0 (- fmt0 distance)) :named p_8)) :named p_7)))
(assert (not (! (not (! (= arg1 (! (+ (! (+ arg0 (! (* 4 (! (s_count (! (- (- fmt1 2) fmt0) :named p_15)) :named p_14)) :named p_13)) :named p_12) (! (* 4 (! (x_count p_15) :named p_17)) :named p_16)) :named p_11)) :named p_10)) :named p_9)))
(assert (not (! (not (! (= 0 p_4) :named p_19)) :named p_18)))
(assert (not (! (not (! (= p_17 p_3) :named p_21)) :named p_20)))
(assert (not p_5))
(assert (not (! (not (! (= 0 fmt0) :named p_23)) :named p_22)))
(assert (not p_7))
(assert (not p_9))
(assert (not p_18))
(assert (not p_20))
(check-sat)
(exit)
