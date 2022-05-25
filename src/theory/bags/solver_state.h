/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags state object.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__THEORY_SOLVER_STATE_H
#define CVC5__THEORY__BAGS__THEORY_SOLVER_STATE_H

#include <map>

#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace bags {

class SolverState : public TheoryState
{
 public:
  SolverState(Env& env, Valuation val);

  /**
   * This function adds the bag representative n to the set d_bags if it is not
   * already there. This function is called during postCheck to collect bag
   * terms in the equality engine. See the documentation of
   * @link SolverState::collectBagsAndCountTerms
   */
  void registerBag(TNode n);

  /**
   * register the pair <element, skolem> with the given bag
   * @param bag a representative of type (Bag E)
   * @param element a representative of type E
   * @param skolem an integer variable
   * @pre (= (bag.count element bag) skolem)
   */
  void registerCountTerm(Node bag, Node element, Node skolem);

  /**
   * store cardinality term and its skolem in a cahce
   * @param n has the form (bag.card A) where A is a representative
   * @param skolem for n
   */
  void registerCardinalityTerm(Node n, Node skolem);

  /**
   * @param n has the form (bag.card A)
   */
  Node getCardinalitySkolem(Node n);

  bool hasCardinalityTerms() const;

  /** get all bag terms that are representatives in the equality engine.
   * This function is valid after the current solver is initialized during
   * postCheck. See SolverState::initialize and BagSolver::postCheck
   */
  const std::set<Node>& getBags();

  /**
   * get all cardinality terms
   * @return a map from registered card terms to their skolem variables
   */
  const std::map<Node, Node>& getCardinalityTerms();

  /**
   * @pre B is a registered bag
   * @return all elements associated with bag B so far
   * Note that associated elements are not necessarily elements in B
   * Example:
   * (assert (= 0 (bag.count x B)))
   * element x is associated with bag B, albeit x is definitely not in B.
   */
  std::set<Node> getElements(Node B);
  /**
   * return disequal bag terms where keys are equality nodes and values are
   * skolems that witness the negation of these equalities
   */
  const std::map<Node, Node>& getDisequalBagTerms();
  /**
   * return a list of bag elements and their skolem counts
   */
  const std::vector<std::pair<Node, Node>>& getElementCountPairs(Node n);

  /** clear all bags data structures */
  void reset();

  /**
   * collect disequal bag terms. This function is called during postCheck.
   */
  void collectDisequalBagTerms();

 private:
  /** constants */
  Node d_true;
  Node d_false;
  /** node manager for this solver state */
  NodeManager* d_nm;
  /** collection of bag representatives */
  std::set<Node> d_bags;
  /**
   * This cache maps bag representatives to pairs of elements and multiplicity
   * skolems which are used for model building.
   * This map is cleared and initialized at the start of each full effort check.
   */
  std::map<Node, std::vector<std::pair<Node, Node>>> d_bagElements;
  /**
   * A map from equalities between bag terms to elements that witness their
   * disequalities. This map is cleared and initialized at the start of each
   * full effort check.
   */
  std::map<Node, Node> d_deq;
  /** a map from card terms to their skolem variables */
  std::map<Node, Node> d_cardTerms;
}; /* class SolverState */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BAGS__THEORY_SOLVER_STATE_H */
