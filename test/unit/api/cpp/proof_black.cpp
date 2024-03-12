/******************************************************************************
 * Top contributors (to current version):
 *   Hans-Jörg Schurr, Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the guards of the C++ API functions.
 */

#include <gtest/gtest.h>

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackProof : public TestApi
{
 protected:
  Proof create_proof()
  {
    d_solver->setOption("produce-proofs", "true");

    Sort uSort = d_tm.mkUninterpretedSort("u");
    Sort intSort = d_tm.getIntegerSort();
    Sort boolSort = d_tm.getBooleanSort();
    Sort uToIntSort = d_tm.mkFunctionSort({uSort}, intSort);
    Sort intPredSort = d_tm.mkFunctionSort({intSort}, boolSort);
    std::vector<Proof> proof;

    Term x = d_tm.mkConst(uSort, "x");
    Term y = d_tm.mkConst(uSort, "y");
    Term f = d_tm.mkConst(uToIntSort, "f");
    Term p = d_tm.mkConst(intPredSort, "p");
    Term zero = d_tm.mkInteger(0);
    Term one = d_tm.mkInteger(1);
    Term f_x = d_tm.mkTerm(Kind::APPLY_UF, {f, x});
    Term f_y = d_tm.mkTerm(Kind::APPLY_UF, {f, y});
    Term sum = d_tm.mkTerm(Kind::ADD, {f_x, f_y});
    Term p_0 = d_tm.mkTerm(Kind::APPLY_UF, {p, zero});
    Term p_f_y = d_tm.mkTerm(Kind::APPLY_UF, {p, f_y});
    d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_x}));
    d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {zero, f_y}));
    d_solver->assertFormula(d_tm.mkTerm(Kind::GT, {sum, one}));
    d_solver->assertFormula(p_0);
    d_solver->assertFormula(p_f_y.notTerm());
    d_solver->checkSat();

    return d_solver->getProof().front();
  }
};

TEST_F(TestApiBlackProof, nullProof)
{
  Proof proof;
  ASSERT_EQ(proof.getRule(), ProofRule::UNKNOWN);

  ASSERT_EQ(std::hash<cvc5::ProofRule>()(ProofRule::UNKNOWN),
            static_cast<size_t>(ProofRule::UNKNOWN));
  ASSERT_TRUE(proof.getResult().isNull());
  ASSERT_TRUE(proof.getChildren().empty());
  ASSERT_TRUE(proof.getArguments().empty());
}

TEST_F(TestApiBlackProof, getRule)
{
  Proof proof = create_proof();
  ASSERT_EQ(proof.getRule(), ProofRule::SCOPE);
}

TEST_F(TestApiBlackProof, getResult)
{
  Proof proof = create_proof();
  ASSERT_NO_THROW(proof.getResult());
}

TEST_F(TestApiBlackProof, getChildren)
{
  Proof proof = create_proof();
  std::vector<Proof> children;
  ASSERT_NO_THROW(children = proof.getChildren());
  ASSERT_FALSE(children.empty());
}

TEST_F(TestApiBlackProof, getArguments)
{
  Proof proof = create_proof();
  ASSERT_NO_THROW(proof.getArguments());
}

}  // namespace test
}  // namespace cvc5::internal
