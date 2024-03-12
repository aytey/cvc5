/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A cache of skolems for theory of strings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__STRINGS__SKOLEM_CACHE_H
#define CVC5__THEORY__STRINGS__SKOLEM_CACHE_H

#include <map>
#include <tuple>
#include <unordered_set>

#include "expr/node.h"
#include "expr/skolem_manager.h"

namespace cvc5::internal {
namespace theory {

class Rewriter;

namespace strings {

/**
 * A cache of all string skolems generated by the TheoryStrings class. This
 * cache is used to ensure that duplicate skolems are not generated when
 * possible, and helps identify what skolems were allocated in the current run.
 */
class SkolemCache
{
 public:
  /**
   * Constructor.
   *
   * @param rr determines if we aggressively share Skolems based on rewriting or
   * return the constants they are entailed to be equal to. This argument is
   * optional.
   */
  SkolemCache(Rewriter* rr);
  /** Identifiers for skolem types
   *
   * The comments below document the properties of each skolem introduced by
   * inference in the strings solver, where by skolem we mean the fresh
   * string variable that witnesses each of "exists k".
   *
   * The skolems with _REV suffixes are used for the reverse version of the
   * preconditions below, e.g. where we are considering a' ++ a = b' ++ b.
   *
   * All skolems assume a and b are strings unless otherwise stated.
   *
   * Notice that these identifiers are each syntax sugar for constructing a
   * purification skolem. It is required for the purposes of proof checking
   * that this only results in calls to SkolemManager::mkPurifySkolem.
   */
  enum SkolemId
  {
    // exists k. k = a
    SK_PURIFY,
    // a != "" ^ b = "ccccd" ^ a ++ "d" ++ a' = b ++ b' =>
    //    exists k. a = "cccc" ++ k
    SK_ID_C_SPT,
    SK_ID_C_SPT_REV,
    // a != "" ^ b = "c" ^ len(a)!=len(b) ^ a ++ a' = b ++ b' =>
    //    exists k. a = "c" ++ k
    SK_ID_VC_SPT,
    SK_ID_VC_SPT_REV,
    // a != "" ^ b != "" ^ len(a)!=len(b) ^ a ++ a' = b ++ b' =>
    //    exists k1 k2. len( k1 )>0 ^ len( k2 )>0 ^
    //                  ( a ++ k1 = b OR a = b ++ k2 )
    // k1 is the variable for (a,b) and k2 is the skolem for (b,a).
    SK_ID_V_SPT,
    SK_ID_V_SPT_REV,
    // a != "" ^ b != "" ^ len(a)!=len(b) ^ a ++ a' = b ++ b' =>
    //    exists k. len( k )>0 ^ ( a ++ k = b OR a = b ++ k )
    SK_ID_V_UNIFIED_SPT,
    SK_ID_V_UNIFIED_SPT_REV,
    // a != ""  ^ b = "c" ^ a ++ a' != b ++ b' =>
    //    exists k, k_rem.
    //         len( k ) = 1 ^
    //         ( ( a = k ++ k_rem ^ k != "c" ) OR ( a = "c" ++ k_rem ) )
    SK_ID_DC_SPT,
    SK_ID_DC_SPT_REM,
    // a != ""  ^ b != "" ^ len( a ) != len( b ) ^ a ++ a' != b ++ b' =>
    //    exists k_x k_y k_z.
    //         ( len( k_y ) = len( a ) ^ len( k_x ) = len( b ) ^ len( k_z) > 0
    //           ( a = k_x ++ k_z OR b = k_y ++ k_z ) )
    SK_ID_DEQ_X,
    SK_ID_DEQ_Y,
    // contains( a, b ) =>
    //    exists k_pre, k_post. a = k_pre ++ b ++ k_post ^
    //                          ~contains(k_pre ++ substr( b, 0, len(b)-1 ), b)
    //
    // As an optimization, these skolems are reused for positive occurrences of
    // contains, where they have the semantics:
    //
    //   contains( a, b ) =>
    //      exists k_pre, k_post. a = k_pre ++ b ++ k_post
    //
    // We reuse them since it is sound to consider w.l.o.g. the first occurrence
    // of b in a as the witness for contains( a, b ).
    SK_FIRST_CTN_PRE,
    SK_FIRST_CTN_POST,
    // For integer b,
    // len( a ) > b =>
    //    exists k. a = k ++ a' ^ len( k ) = b
    SK_PREFIX,
    // For integer b,
    // b > 0 =>
    //    exists k. a = a' ++ k ^ len( k ) = ite( len(a)>b, len(a)-b, 0 )
    SK_SUFFIX_REM
  };
  /**
   * Returns a skolem of type string that is cached for (a,b,id) and has
   * name c.
   */
  Node mkSkolemCached(Node a, Node b, SkolemId id, const char* c);
  /**
   * Returns a skolem of type string that is cached for (a,[null],id) and has
   * name c.
   */
  Node mkSkolemCached(Node a, SkolemId id, const char* c);
  /** Same as above, but the skolem to construct has a custom type tn */
  Node mkTypedSkolemCached(
      TypeNode tn, Node a, Node b, SkolemId id, const char* c);
  /** Same as mkTypedSkolemCached above for (a,[null],id) */
  Node mkTypedSkolemCached(TypeNode tn, Node a, SkolemId id, const char* c);
  /** Returns a (uncached) skolem of type string with name c */
  Node mkSkolem(const char* c);
  /** Returns true if n is a skolem allocated by this class */
  bool isSkolem(Node n) const;
  /** Make index variable
   *
   * This returns an integer variable of kind BOUND_VARIABLE that is used
   * for axiomatizing the behavior of a term or predicate t. Notice that this
   * index variable does *not* necessarily refer to indices in the term t
   * itself. Instead, it refers to indices in the relevant string in the
   * reduction of t. For example, the index variable for the term str.to_int(s)
   * is used to quantify over the positions in string term s.
   */
  static Node mkIndexVar(Node t);

  /** Make length variable
   *
   * This returns an integer variable of kind BOUND_VARIABLE that is used for
   * axiomatizing the behavior of a term or predicate t. It refers to lengths
   * of strings in the reduction of t. For example, the length variable for the
   * term str.indexof(s, r, n) is used to quantify over the lengths of strings
   * that could be matched by r.
   */
  static Node mkLengthVar(Node t);
  /**
   * Make skolem function, possibly normalizing based on the rewriter of this
   * class. This method should be used whenever it is not possible to define
   * a Skolem identifier that amounts to purification of a term.
   *
   * Notice that this method is not static or constant since it tracks the
   * Skolem we construct (in d_allSkolems), which is used for finite model
   * finding.
   */
  Node mkSkolemFun(SkolemFunId id,
                   Node a = Node::null(),
                   Node b = Node::null());

 private:
  /**
   * Simplifies the arguments for a string skolem used for indexing into the
   * cache. In certain cases, we can share skolems with similar arguments e.g.
   * SK_FIRST_CTN(a, c) can be used instead of SK_FIRST_CTN((str.substr a 0 n),
   * c) because the first occurrence of "c" in "(str.substr a 0 n)" is also the
   * first occurrence of "c" in "a" (assuming that "c" appears in both and
   * otherwise the value of SK_FIRST_CTN does not matter).
   *
   * @param id The type of skolem
   * @param a The first argument used for indexing
   * @param b The second argument used for indexing
   * @return A tuple with the new skolem id, the new first, and the new second
   * argument
   */
  std::tuple<SkolemId, Node, Node> normalizeStringSkolem(SkolemId id,
                                                         Node a,
                                                         Node b);
  /** the optional rewriter */
  Rewriter* d_rr;
  /** string type */
  TypeNode d_strType;
  /** Constant node zero */
  Node d_zero;
  /** map from node pairs and identifiers to skolems */
  std::map<Node, std::map<Node, std::map<SkolemId, Node> > > d_skolemCache;
  /** the set of all skolems we have generated */
  std::unordered_set<Node> d_allSkolems;
  /**
   * Get cache vals, which returns the vector of terms from (possibly null)
   * a and b that should be passed to the skolem manager.
   */
  std::vector<Node> getSkolemCacheVals(const Node& a, const Node& b) const;
};

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__SKOLEM_CACHE_H */
