/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mudathir Mohamed, Kshitij Bansal
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Skolem manager utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__EXPR__SKOLEM_MANAGER_H
#define CVC5__EXPR__SKOLEM_MANAGER_H

#include <string>

#include "expr/node.h"

namespace cvc5::internal {

class ProofGenerator;

/** Skolem function identifier */
enum class SkolemFunId
{
  NONE,
  /** An internal skolem */
  INTERNAL,
  /** input variable with a given name */
  INPUT_VARIABLE,
  /** purification skolem for a term t */
  PURIFY,
  /** abstract value for a term t */
  ABSTRACT_VALUE,
  /** array diff to witness (not (= A B)) */
  ARRAY_DEQ_DIFF,
  /** an uninterpreted function f s.t. f(x) = x / 0.0 (real division) */
  DIV_BY_ZERO,
  /** an uninterpreted function f s.t. f(x) = x / 0 (integer division) */
  INT_DIV_BY_ZERO,
  /** an uninterpreted function f s.t. f(x) = x mod 0 */
  MOD_BY_ZERO,
  /** an uninterpreted function f s.t. f(x) = sqrt(x) */
  SQRT,
  /**
   * Argument used to purify trancendental function app f(x).
   * For sin(x), this is a variable that is assumed to be in phase with x that
   * is between -pi and pi
   */
  TRANSCENDENTAL_PURIFY_ARG,
  /**
   * The n^th skolem for quantified formula Q. Its arguments are (Q,n).
   */
  QUANTIFIERS_SKOLEMIZE,
  //----- string skolems are cached based on (a, b)
  /** exists k. ( string b occurs k times in string a ) */
  STRINGS_NUM_OCCUR,
  /** exists k. ( regular expression b can be matched k times in a ) */
  STRINGS_NUM_OCCUR_RE,
  /** For function k: Int -> Int
   *   exists k.
   *     forall 0 <= x <= n,
   *       k(x) is the end index of the x^th occurrence of b in a
   *   where n is the number of occurrences of b in a, and k(0)=0.
   */
  STRINGS_OCCUR_INDEX,
  /** Same, but where b is a regular expression */
  STRINGS_OCCUR_INDEX_RE,
  /**
   * For function k: Int -> Int
   *   exists k.
   *     forall 0 <= x < n,
   *       k(x) is the length of the x^th occurrence of b in a (excluding
   *       matches of empty strings)
   *   where b is a regular expression, n is the number of occurrences of b
   *   in a, and k(0)=0.
   */
  STRINGS_OCCUR_LEN,
  /** Same, but where b is a regular expression */
  STRINGS_OCCUR_LEN_RE,
  /**
   * Diff index for disequalities a != b => substr(a,k,1) != substr(b,k,1)
   */
  STRINGS_DEQ_DIFF,
  //-----
  /**
   * A function used to define intermediate results of str.replace_all and
   * str.replace_re_all applications.
   */
  STRINGS_REPLACE_ALL_RESULT,
  /**
   * A function used to define intermediate results of str.from_int
   * applications.
   */
  STRINGS_ITOS_RESULT,
  /**
   * A function used to define intermediate results of str.to_int
   * applications.
   */
  STRINGS_STOI_RESULT,
  /**
   * An index containing a non-digit in a string, used when (str.to_int a) = -1.
   */
  STRINGS_STOI_NON_DIGIT,
  /**
   * For sequence a and regular expression b,
   * in_re(a, re.++(_*, b, _*)) =>
   *    exists k_pre, k_match, k_post.
   *       a = k_pre ++ k_match ++ k_post ^
   *       len(k_pre) = indexof_re(x, y, 0) ^
   *       (forall l. 0 < l < len(k_match) =>
   *         ~in_re(substr(k_match, 0, l), r)) ^
   *       in_re(k_match, b)
   *
   * k_pre is the prefix before the first, shortest match of b in a. k_match
   * is the substring of a matched by b. It is either empty or there is no
   * shorter string that matches b.
   */
  RE_FIRST_MATCH_PRE,
  RE_FIRST_MATCH,
  RE_FIRST_MATCH_POST,
  /**
   * Regular expression unfold component: if (str.in_re t R), where R is
   * (re.++ r0 ... rn), then the RE_UNFOLD_POS_COMPONENT{t,R,i} is a string
   * skolem ki such that t = (str.++ k0 ... kn) and (str.in_re k0 r0) for
   * i = 0, ..., n.
   */
  RE_UNFOLD_POS_COMPONENT,
  /**
   * An uninterpreted function for bag.card operator:
   * To compute (bag.card A), we need a function that
   * counts multiplicities of distinct elements. We call this function
   * combine of type Int -> Int where:
   * combine(0) = 0.
   * combine(i) = m(elements(i), A) + combine(i-1) for 1 <= i <= n.
   * elements: a skolem function for (bag.fold f t A)
   *            see BAGS_CARD_ELEMENTS.
   * n: is the number of distinct elements in A.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` the bag argument A.
   */
  BAGS_CARD_COMBINE,
  /**
   * An uninterpreted function for bag.card operator:
   * To compute (bag.card A), we need a function for
   * distinct elements in A. We call this function
   * elements of type Int -> T where T is the type of
   * elements of A.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` the bag argument A.
   */
  BAGS_CARD_ELEMENTS,
  /**
   * An uninterpreted function for bag.card operator:
   * To compute (bag.card A), we need to guess n
   * the number of distinct elements in A.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` the bag argument A.
   */
  BAGS_CARD_N,
  /**
   * An uninterpreted function for bag.card operator:
   * To compute (bag.card A), we need a function for
   * distinct elements in A which is given by elements defined in
   * BAGS_CARD_ELEMENTS.
   * We also need unionDisjoint: Int -> (Bag T) to compute
   * the disjoint union such that:
   * unionDisjoint(0) = bag.empty.
   * unionDisjoint(i) = disjoint union of {<elements(i), m(elements(i), A)>}
   * and unionDisjoint(i-1).
   * unionDisjoint(n) = A.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` the bag argument A.
   */
  BAGS_CARD_UNION_DISJOINT,
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute (bag.fold f t A), we need to guess the cardinality n of
   * bag A using a skolem function with BAGS_FOLD_CARD id.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` the bag argument A.
   */
  BAGS_FOLD_CARD,
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute (bag.fold f t A), we need a function that
   * accumulates intermidiate values. We call this function
   * combine of type Int -> T2 where:
   * combine(0) = t
   * combine(i) = f(elements(i), combine(i - 1)) for 1 <= i <= n.
   * elements: a skolem function for (bag.fold f t A)
   *           see BAGS_FOLD_ELEMENTS.
   * n: is the cardinality of A.
   * T2: is the type of initial value t.
   *
   * - Number of skolem arguments: ``3``
   *   - ``1:`` the function f of type T1 -> T2.
   *   - ``2:`` the initial value t of type T2.
   *   - ``3:`` the bag argument A of type (Bag T1).
   */
  BAGS_FOLD_COMBINE,
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute (bag.fold f t A), we need a function for
   * elements of A. We call this function
   * elements of type Int -> T1 where T1 is the type of
   * elements of A.
   * If the cardinality of A is n, then
   * A is the disjoint union of {<elements(i),1>} for 1 <= i <= n.
   * See BAGS_FOLD_UNION_DISJOINT.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` a bag argument A.
   */
  BAGS_FOLD_ELEMENTS,
  /**
   * An uninterpreted function for bag.fold operator:
   * To compute (bag.fold f t A), we need a function for
   * elements of A which is given by elements defined in
   * BAGS_FOLD_ELEMENTS.
   * We also need unionDisjoint: Int -> (Bag T1) to compute
   * the disjoint union such that:
   * unionDisjoint(0) = bag.empty.
   * unionDisjoint(i) = disjoint union of {elements(i)} and unionDisjoint (i-1).
   * unionDisjoint(n) = A.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` the bag argument A.
   */
  BAGS_FOLD_UNION_DISJOINT,
  /**
   * An interpreted function for bag.choose operator:
   * (bag.choose A) is expanded as
   * (witness ((x elementType))
   *    (ite
   *      (= A (as emptybag (Bag E)))
   *      (= x (uf A))
   *      (and (>= (bag.count x A) 1) (= x (uf A)))
   * where uf: (Bag E) -> E is a skolem function, and E is the type of elements
   * of A.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` a ground value for the type (Bag E).
   */
  BAGS_CHOOSE,
  /**
   * An uninterpreted function for bag.map operator:
   * To compute (bag.count y (bag.map f A)), we need to find the distinct
   * elements in A that are mapped to y by function f (i.e., preimage of {y}).
   * If n is the cardinality of this preimage, then
   * the preimage is the set {uf(1), ..., uf(n)}
   * where uf: Int -> E is a skolem function, and E is the type of elements of
   * A.
   *
   * - Number of skolem arguments: ``3``
   *   - ``1:`` the function f of type E -> T.
   *   - ``2:`` the bag argument A of (Bag E).
   *   - ``3:`` the element argument e type T.
   */
  BAGS_MAP_PREIMAGE,
  /**
   * Same as above, but used when f is injective.
   * The returned skolem is an element representing preimage of {y}.
   *
   * - Number of skolem arguments: ``3``
   *   - ``1:`` the function f of type E -> T.
   *   - ``2:`` the bag argument A of (Bag E).
   *   - ``3:`` the element argument e type E.
   */
  BAGS_MAP_PREIMAGE_INJECTIVE,
  /**
   * A skolem variable for the size of the preimage of {y} that is unique per
   * terms (bag.map f A), y which might be an element in (bag.map f A). (see the
   * documentation for BAGS_MAP_PREIMAGE).
   *
   * - Number of skolem arguments: ``3``
   *   - ``1:`` the function f of type E -> T.
   *   - ``2:`` the bag argument A of (Bag E).
   *   - ``3:`` the element argument e type E.
   */
  BAGS_MAP_PREIMAGE_SIZE,
  /**
   * A skolem variable for the index that is unique per terms
   * (bag.map f A), y, preImageSize, y, e which might be an element in A.
   * (see the documentation for BAGS_MAP_PREIMAGE).
   *
   * - Number of skolem arguments: ``5``
   *   - ``1:`` a map term of the form (bag.map f A)
   *   - ``2:`` a skolem function with id BAGS_MAP_PREIMAGE
   *   - ``3:`` a skolem function with id BAGS_MAP_PREIMAGE_SIZE.
   *   - ``4:`` an element y of type T representing the mapped value.
   *   - ``5:`` an element x of type E.
   */
  BAGS_MAP_PREIMAGE_INDEX,
  /**
   * An uninterpreted function for bag.map operator:
   * If the preimage of {y} in A is {uf(1), ..., uf(n)} (see BAGS_MAP_PREIMAGE},
   * then the multiplicity of an element y in a bag (map f A) is sum(n),
   * where sum: Int -> Int is a skolem function such that:
   * sum(0) = 0
   * sum(i) = sum (i-1) + (bag.count (uf i) A)
   *
   * - Number of skolem arguments: ``3``
   *   - ``1:`` the function f of type E -> T.
   *   - ``2:`` the bag argument A of (Bag E).
   *   - ``3:`` the element argument e type E.
   */
  BAGS_MAP_SUM,
  /**
   * bag diff to witness (not (= A B)).
   *
   * - Number of skolem arguments: ``2``
   *   - ``1:`` the first bag.
   *   - ``2:`` the second bag.
   */
  BAGS_DEQ_DIFF,
  /**
   * Given a group term ((_ table.group n1 ... nk) A) of type (Bag (Table T))
   * this uninterpreted function maps elements of A to their parts in the
   * resulting partition. It has type (-> T (Table T))
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` a group term of the form ((_ table.group n1 ... nk) A).
   */
  TABLES_GROUP_PART,
  /**
   * Given a group term ((_ table.group n1 ... nk) A) of type (Bag (Table T))
   * and a part B of type (Table T), this function returns a skolem element
   * that is a member of B if B is not empty.
   *
   * - Number of skolem arguments: ``2``
   *   - ``1:`` a group term of the form ((_ table.group n1 ... nk) A).
   *   - ``2:`` a table B of type (Table T).
   */
  TABLES_GROUP_PART_ELEMENT,
  /**
   * Given a group term ((_ rel.group n1 ... nk) A) of type (Set (Relation T))
   * this uninterpreted function maps elements of A to their parts in the
   * resulting partition. It has type (-> T (Relation T))
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` a relation of the form ((_ rel.group n1 ... nk) A).
   */
  RELATIONS_GROUP_PART,
  /**
   * Given a group term ((_ rel.group n1 ... nk) A) of type (Set (Relation T))
   * and a part B of type (Relation T), this function returns a skolem element
   * that is a member of B if B is not empty.
   * - Number of skolem arguments: ``2``
   *   - ``1:`` a group term of the form ((_ rel.group n1 ... nk) A).
   *   - ``2:`` a relation B of type (Relation T).
   */
  RELATIONS_GROUP_PART_ELEMENT,
  /**
   * An interpreted function for set.choose operator:
   * (set.choose A) is expanded as
   * (witness ((x elementType))
   *    (ite
   *      (= A (as set.empty (Set E)))
   *      (= x (uf A))
   *      (and (set.member x A) (= x uf(A)))
   * where uf: (Set E) -> E is a skolem function, and E is the type of elements
   * of A
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` a ground value for the type (Set E).
   */
  SETS_CHOOSE,
  /**
   * set diff to witness (not (= A B))
   * - Number of skolem arguments: ``2``
   *   - ``1:`` the first set.
   *   - ``2:`` the second set.
   */
  SETS_DEQ_DIFF,
  /**
   * An uninterpreted function for set.fold operator:
   * To compute (set.fold f t A), we need to guess the cardinality n of
   * set A using a skolem function with SETS_FOLD_CARD id.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` the set argument A.
   */
  SETS_FOLD_CARD,
  /**
   * An uninterpreted function for set.fold operator:
   * To compute (set.fold f t A), we need a function that
   * accumulates intermidiate values. We call this function
   * combine of type Int -> T2 where:
   * combine(0) = t
   * combine(i) = f(elements(i), combine(i - 1)) for 1 <= i <= n
   * elements: a skolem function for (set.fold f t A)
   *           see SETS_FOLD_ELEMENTS
   * n: is the cardinality of A
   * T2: is the type of initial value t
   *
   * - Number of skolem arguments: ``3``
   *   - ``1:`` the function f of type T1 -> T2.
   *   - ``2:`` the initial value t of type T2.
   *   - ``3:`` the set argument A of type (Set T1).
   */
  SETS_FOLD_COMBINE,
  /**
   * An uninterpreted function for set.fold operator:
   * To compute (set.fold f t A), we need a function for
   * elements of A. We call this function
   * elements of type Int -> T1 where T1 is the type of
   * elements of A.
   * If the cardinality of A is n, then
   * A is the union of {elements(i)} for 1 <= i <= n.
   * See SETS_FOLD_UNION_DISJOINT.
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` a set argument A.
   */
  SETS_FOLD_ELEMENTS,
  /**
   * An uninterpreted function for set.fold operator:
   * To compute (set.fold f t A), we need a function for
   * elements of A which is given by elements defined in
   * SETS_FOLD_ELEMENTS.
   * We also need unionFn: Int -> (Set T1) to compute
   * the union such that:
   * unionFn(0) = set.empty
   * unionFn(i) = union of {elements(i)} and unionFn (i-1)
   * unionFn(n) = A
   *
   * - Number of skolem arguments: ``1``
   *   - ``1:`` a set argument A.
   */
  SETS_FOLD_UNION,
  /**
   * A skolem variable that is unique per terms (set.map f A), y which is an
   * element in (set.map f A). The skolem is constrained to be an element in A,
   * and it is mapped to y by f.
   *
   * - Number of skolem arguments: ``2``
   *   - ``1:`` a map term of the form (set.map f A)
   *   - ``3:`` the element argument y.
   */
  SETS_MAP_DOWN_ELEMENT,
  /** a shared selector */
  SHARED_SELECTOR,
  UNKNOWN
};
/** Converts a skolem function name to a string. */
const char* toString(SkolemFunId id);
/** Writes a skolem function name to a stream. */
std::ostream& operator<<(std::ostream& out, SkolemFunId id);

/**
 * Internal skolem function identifier, used for identifying internal skolems
 * that are not exported as part of the API.
 *
 * This is a subclassification of skolems whose SkolemFunId is INTERNAL. It is
 * used to generate canonical skolems but without exporting to the API. Skolems
 * can be created using mkInternalSkolemFunction below.
 */
enum class InternalSkolemFunId
{
  NONE,
  /** Sequence model construction, element for base */
  SEQ_MODEL_BASE_ELEMENT,
  /** the "none" term, for instantiation evaluation */
  IEVAL_NONE,
  /** the "some" term, for instantiation evaluation */
  IEVAL_SOME,
  /** sygus "any constant" placeholder */
  SYGUS_ANY_CONSTANT,
  /**
   * Quantifiers synth fun embedding, for function-to-synthesize, this the
   * first order datatype variable for f.
   */
  QUANTIFIERS_SYNTH_FUN_EMBED,
  /** Higher-order type match predicate, see HoTermDb */
  HO_TYPE_MATCH_PRED
};
/** Converts an internal skolem function name to a string. */
const char* toString(InternalSkolemFunId id);
/** Writes an internal skolem function name to a stream. */
std::ostream& operator<<(std::ostream& out, InternalSkolemFunId id);

/**
 * A manager for skolems that can be used in proofs. This is designed to be
 * a trusted interface for constructing variables of SKOLEM type, where one
 * must provide information that characterizes the skolem. This information
 * may either be:
 * (1) the term that the skolem purifies (`mkPurifySkolem`)
 * (2) an identifier (`mkSkolemFunction`) and a set of "cache values", which
 * can be seen as arguments to the skolem function. These are typically used for
 * implementing theory-specific inferences that introduce symbols that
 * are not interpreted by the theory (see SkolemFunId enum).
 *
 * Note that (1) is a special instance of (2), where the purification skolem
 * for t is equivalent to calling mkSkolemFunction on SkolemFunId::PURIFY
 * and t.
 *
 * If a variable cannot be associated with any of the above information,
 * the method `mkDummySkolem` may be used, which always constructs a fresh
 * skolem variable.
 *
 * It is implemented by mapping terms to an attribute corresponding to their
 * "original form" as described below. Hence, this class does not impact the
 * reference counting of skolem variables which may be deleted if they are not
 * used.
 *
 * To handle purification of witness terms, notice that the purification
 * skolem for (witness ((x T)) P) is equivalent to the skolem function:
 *    (QUANTIFIERS_SKOLEMIZE (exists ((x T)) P) 0)
 * In other words, the purification for witness terms are equivalent to
 * the skolemization of their corresponding existential. This is currently only
 * used for eliminating witness terms coming from algorithms that introduce
 * them, e.g. BV/set instantiation. Unifying these two skolems is required
 * for ensuring proof checking succeeds for term formula removal on witness
 * terms.
 *
 * The use of purification skolems and skolem functions avoid having to reason
 * about witness terms. This avoids several complications. In particular,
 * witness terms in most contexts should be seen as black boxes, converting
 * something to a witness term may have unintended consequences e.g. variable
 * shadowing. In contrast, converting to original form does not have these
 * complications. Furthermore, having original form greatly simplifies
 * reasoning in the proof in certain external proof formats, in particular, it
 * avoids the need to reason about identifiers for introduced variables for
 * the binders of witness terms.
 */
class SkolemManager
{
 public:
  SkolemManager();
  ~SkolemManager() {}

  /**
   * Optional flags used to control behavior of skolem creation.
   * They should be composed with a bitwise OR.
   */
  enum SkolemFlags
  {
    /** default behavior */
    SKOLEM_DEFAULT = 0,
    /** do not make the name unique by adding the id */
    SKOLEM_EXACT_NAME = 1,
  };
  /**
   * Make purification skolem. This skolem is unique for each t, which we
   * implement via an attribute on t. This attribute is used to ensure to
   * associate a unique skolem for each t.
   *
   * Notice that a purification skolem is trivial to justify (via
   * SKOLEM_INTRO), and hence it does not require a proof generator.
   *
   * Notice that we do not convert t to original form in this call. Thus,
   * in very rare cases, two Skolems may be introduced that have the same
   * original form. For example, let k be the skolem introduced to eliminate
   * (ite A B C). Then, asking for the purify skolem for:
   *  (ite (ite A B C) D E) and (ite k D E)
   * will return two different Skolems.
   *
   * @param t The term to purify
   * @param pg The proof generator for the skolemization of t. This should
   * only be provided if t is a witness term (witness ((x T)) P). If non-null,
   * this proof generator must respond to a call to getProofFor on
   * (exists ((x T)) P) during the lifetime of the current node manager.
   * @return The purification skolem for t
   */
  Node mkPurifySkolem(Node t,
                      ProofGenerator* pg = nullptr);
  /**
   * Make skolem function. This method should be used for creating fixed
   * skolem functions of the forms described in SkolemFunId. The user of this
   * method is responsible for providing a proper type for the identifier that
   * matches the description of id. Skolem functions are useful for modelling
   * the behavior of partial functions, or for theory-specific inferences that
   * introduce fresh variables.
   *
   * A skolem function is not given a formal semantics in terms of a witness
   * term, nor is it a purification skolem, thus it does not fall into the two
   * categories of skolems above. This method is motivated by convenience, as
   * the user of this method does not require constructing canonical variables
   * for witness terms.
   *
   * The returned skolem is an ordinary skolem variable that can be used
   * e.g. in APPLY_UF terms when tn is a function type.
   *
   * Notice that we do not insist that tn is a function type. A user of this
   * method may construct a canonical (first-order) skolem using this method
   * as well.
   *
   * @param id The identifier of the skolem function
   * @param cacheVal A cache value. The returned skolem function will be
   * unique to the pair (id, cacheVal). This value is required, for instance,
   * for skolem functions that are in fact families of skolem functions,
   * e.g. the wrongly applied case of selectors.
   * @return The skolem function.
   */
  Node mkSkolemFunction(SkolemFunId id,
                        Node cacheVal = Node::null());
  /** Same as above, with multiple cache values */
  Node mkSkolemFunction(SkolemFunId id, const std::vector<Node>& cacheVals);
  /**
   * Same as above, with multiple cache values and an internal skolem id.
   * This will call mkSkolemFunction where the (external) id is
   * SkolemFunId::INTERNAL. The type is provided explicitly.
   */
  Node mkInternalSkolemFunction(InternalSkolemFunId id,
                                TypeNode tn,
                                const std::vector<Node>& cacheVals = {});
  /**
   * Is k a skolem function? Returns true if k was generated by the above
   * call. Updates the arguments to the values used when constructing it.
   */
  bool isSkolemFunction(TNode k, SkolemFunId& id, Node& cacheVal) const;
  /**
   * Get skolem function id
   */
  SkolemFunId getId(TNode k) const;
  /**
   * Get the internal skolem function id, for skolems whose id is
   * SkolemFunId::INTERNAL.
   */
  InternalSkolemFunId getInternalId(TNode k) const;
  /**
   * Create a skolem constant with the given name, type, and comment. This
   * should only be used if the definition of the skolem does not matter.
   * The definition of a skolem matters e.g. when the skolem is used in a
   * proof.
   *
   * @param prefix the name of the new skolem variable is the prefix
   * appended with a unique ID.  This way a family of skolem variables
   * can be made with unique identifiers, used in dump, tracing, and
   * debugging output.  Use SKOLEM_EXACT_NAME flag if you don't want
   * a unique ID appended and use prefix as the name.
   * @param type the type of the skolem variable to create
   * @param comment a comment for dumping output; if declarations are
   * being dumped, this is included in a comment before the declaration
   * and can be quite useful for debugging
   * @param flags an optional mask of bits from SkolemFlags to control
   * skolem behavior
   */
  Node mkDummySkolem(const std::string& prefix,
                     const TypeNode& type,
                     const std::string& comment = "",
                     int flags = SKOLEM_DEFAULT);
  /**
   * Get proof generator for existentially quantified formula q. This returns
   * the proof generator that was provided in a call to `mkSkolemize` above.
   */
  ProofGenerator* getProofGenerator(Node q) const;
  /** Returns true if n is a skolem that stands for an abstract value */
  bool isAbstractValue(TNode n) const;
  /**
   * Convert to original form, which recursively replaces all skolems terms in
   * n by the term they purify.
   *
   * @param n The term or formula to convert to original form described above
   * @return n in original form.
   */
  static Node getOriginalForm(Node n);
  /**
   * Convert to unpurified form, which returns the term that k purifies. This
   * is literally the term that was passed as an argument to mkPurify on the
   * call that created k. In contrast to getOriginalForm, this is not
   * recursive w.r.t. skolems, so that the term purified by k may itself
   * contain purification skolems that are not expanded.
   *
   * @param k The skolem to convert to unpurified form
   * @return the unpurified form of k.
   */
  static Node getUnpurifiedForm(Node k);

 private:
  /** Cache of skolem functions for mkSkolemFunction above. */
  std::map<std::tuple<SkolemFunId, TypeNode, Node>, Node> d_skolemFuns;
  /** Backwards mapping of above */
  std::map<Node, std::tuple<SkolemFunId, TypeNode, Node>> d_skolemFunMap;
  /**
   * Mapping from witness terms to proof generators.
   */
  std::map<Node, ProofGenerator*> d_gens;

  /**
   * A counter used to produce unique skolem names.
   *
   * Note that it is NOT incremented when skolems are created using
   * SKOLEM_EXACT_NAME, so it is NOT a count of the skolems produced
   * by this node manager.
   */
  size_t d_skolemCounter;
  /** Same as mkSkolemFunction, with explicit type */
  Node mkSkolemFunctionTyped(SkolemFunId id,
                             TypeNode tn,
                             Node cacheVal = Node::null());
  /** Same as above, with multiple cache values and explicit Type */
  Node mkSkolemFunctionTyped(SkolemFunId id,
                             TypeNode tn,
                             const std::vector<Node>& cacheVals);
  /**
   * Create a skolem constant with the given name, type, and comment.
   *
   * This method is intentionally private. To create skolems, one should
   * call a public method from SkolemManager for allocating a skolem in a
   * proper way, or otherwise use SkolemManager::mkDummySkolem.
   */
  Node mkSkolemNode(Kind k,
                    const std::string& prefix,
                    const TypeNode& type,
                    int flags = SKOLEM_DEFAULT);
  /** Get type for skolem */
  TypeNode getTypeFor(SkolemFunId id, const std::vector<Node>& cacheVals);
};

}  // namespace cvc5::internal

#endif /* CVC5__EXPR__PROOF_SKOLEM_CACHE_H */
