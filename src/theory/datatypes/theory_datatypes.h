/*********************                                                        */
/*! \file theory_datatypes.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Francois Bobot, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Theory of datatypes.
 **
 ** Theory of datatypes.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H
#define __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H

#include "theory/theory.h"
#include "util/datatype.h"
#include "util/hash.h"
#include "util/trans_closure.h"
#include "theory/uf/equality_engine.h"

#include <ext/hash_set>
#include <iostream>
#include <map>
#include "context/cdchunk_list.h"

namespace CVC4 {
namespace theory {
namespace datatypes {

class EqualityQueryTheory;

class TheoryDatatypes : public Theory {
  friend class EqualityQueryTheory;
private:
  typedef context::CDChunkList<Node> NodeList;
  typedef context::CDHashMap<Node, NodeList*, NodeHashFunction> NodeListMap;
  typedef context::CDHashMap< Node, bool, NodeHashFunction > BoolMap;

  /** transitive closure to record equivalence/subterm relation.  */
  //TransitiveClosureNode d_cycle_check;
  /** has seen cycle */
  context::CDO< bool > d_hasSeenCycle;
  /** inferences */
  NodeList d_infer;
  NodeList d_infer_exp;
  Node d_true;
  /** mkAnd */
  Node mkAnd( std::vector< TNode >& assumptions );
private:
  //notification class for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryDatatypes& d_dt;
  public:
    NotifyClass(TheoryDatatypes& dt): d_dt(dt) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) {
      Debug("dt") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
      if (value) {
        return d_dt.propagate(equality);
      } else {
        // We use only literal triggers so taking not is safe
        return d_dt.propagate(equality.notNode());
      }
    }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) {
      Debug("dt") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_dt.propagate(predicate);
      } else {
       return d_dt.propagate(predicate.notNode());
      }
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
      Debug("dt") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
      if (value) {
        return d_dt.propagate(t1.eqNode(t2));
      } else {
        return d_dt.propagate(t1.eqNode(t2).notNode());
      }
    }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) {
      Debug("dt") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_dt.conflict(t1, t2);
    }
    void eqNotifyNewClass(TNode t) {
      Debug("dt") << "NotifyClass::eqNotifyNewClass(" << t << std::endl;
      d_dt.eqNotifyNewClass(t);
    }
    void eqNotifyPreMerge(TNode t1, TNode t2) {
      Debug("dt") << "NotifyClass::eqNotifyPreMerge(" << t1 << ", " << t2 << std::endl;
      d_dt.eqNotifyPreMerge(t1, t2);
    }
    void eqNotifyPostMerge(TNode t1, TNode t2) {
      Debug("dt") << "NotifyClass::eqNotifyPostMerge(" << t1 << ", " << t2 << std::endl;
      d_dt.eqNotifyPostMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
      Debug("dt") << "NotifyClass::eqNotifyDisequal(" << t1 << ", " << t2 << ", " << reason << std::endl;
      d_dt.eqNotifyDisequal(t1, t2, reason);
    }
  };/* class TheoryDatatypes::NotifyClass */
private:
  /** equivalence class info
   * d_inst is whether the instantiate rule has been applied,
   * d_constructor is a node of kind APPLY_CONSTRUCTOR (if any) in this equivalence class,
   * d_selectors is whether a selector has been applied to this equivalence class.
   */
  class EqcInfo
  {
  public:
    EqcInfo( context::Context* c );
    ~EqcInfo(){}
    //whether we have instantiatied this eqc
    context::CDO< bool > d_inst;
    //constructor equal to this eqc
    context::CDO< Node > d_constructor;
    //all selectors whose argument is this eqc
    context::CDO< bool > d_selectors;
  };
  /** does eqc of n have a label (do we know its constructor)? */
  bool hasLabel( EqcInfo* eqc, Node n );
  /** get the label associated to n */
  Node getLabel( Node n );
  /** get the index of the label associated to n */
  int getLabelIndex( EqcInfo* eqc, Node n );
  /** does eqc of n have any testers? */
  bool hasTester( Node n );
  /** get the possible constructors for n */
  void getPossibleCons( EqcInfo* eqc, Node n, std::vector< bool >& cons );
private:
  /** The notify class */
  NotifyClass d_notify;
  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;
  /** information necessary for equivalence classes */
  std::map< Node, EqcInfo* > d_eqc_info;
  /** map from nodes to their instantiated equivalent for each constructor type */
  std::map< Node, std::map< int, Node > > d_inst_map;
  /** which instantiation lemmas we have sent */
  std::map< Node, std::vector< Node > > d_inst_lemmas;
  /** labels for each equivalence class
   * for each eqc n, d_labels[n] is testers that hold for this equivalence class, either:
   * a list of equations of the form
   *   NOT is_[constructor_1]( t )...NOT is_[constructor_n]( t ), each of which are unique testers
   *   and n is less than the number of possible constructors for t minus one,
   * or a list of equations of the form
   *   NOT is_[constructor_1]( t )...NOT is_[constructor_n]( t )  followed by
   *   is_[constructor_(n+1)]( t ), each of which is a unique tester.
  */
  NodeListMap d_labels;
  /** selector apps for eqch equivalence class */
  NodeListMap d_selector_apps;
  /** constructor terms */
  BoolMap d_consEqc;
  /** Are we in conflict */
  context::CDO<bool> d_conflict;
  /** The conflict node */
  Node d_conflictNode;
  /** cache for which terms we have called collectTerms(...) on */
  BoolMap d_collectTermsCache;
  /** pending assertions/merges */
  std::vector< Node > d_pending;
  std::map< Node, Node > d_pending_exp;
  std::vector< Node > d_pending_merge;
  /** expand definition skolem functions */
  std::map< Node, Node > d_exp_def_skolem;
  /** All the constructor terms that the theory has seen */
  context::CDList<TNode> d_consTerms;
  /** All the selector terms that the theory has seen */
  context::CDList<TNode> d_selTerms;
  /** counter for forcing assignments (ensures fairness) */
  unsigned d_dtfCounter;
private:
  /** assert fact */
  void assertFact( Node fact, Node exp );
  /** flush pending facts */
  void flushPendingFacts();
  /** do pending merged */
  void doPendingMerges();
  /** get or make eqc info */
  EqcInfo* getOrMakeEqcInfo( TNode n, bool doMake = false );
  /** has eqc info */
  bool hasEqcInfo( TNode n ) { return d_labels.find( n )!=d_labels.end(); }
  /** get eqc constructor */
  TNode getEqcConstructor( TNode r );
protected:
  /** compute care graph */
  void computeCareGraph();
public:
  TheoryDatatypes(context::Context* c, context::UserContext* u,
                  OutputChannel& out, Valuation valuation,
                  const LogicInfo& logicInfo);
  ~TheoryDatatypes();

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  /** propagate */
  void propagate(Effort effort);
  /** propagate */
  bool propagate(TNode literal);
  /** explain */
  void addAssumptions( std::vector<TNode>& assumptions, std::vector<TNode>& tassumptions );
  void explainEquality( TNode a, TNode b, bool polarity, std::vector<TNode>& assumptions );
  void explainPredicate( TNode p, bool polarity, std::vector<TNode>& assumptions );
  void explain( TNode literal, std::vector<TNode>& assumptions );
  Node explain( TNode literal );
  Node explain( std::vector< Node >& lits );
  /** Conflict when merging two constants */
  void conflict(TNode a, TNode b);
  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);
  /** called when two equivalance classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);
  /** called when two equivalance classes have merged */
  void eqNotifyPostMerge(TNode t1, TNode t2);
  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

  void check(Effort e);
  void preRegisterTerm(TNode n);
  Node expandDefinition(LogicRequest &logicRequest, Node n);
  Node ppRewrite(TNode n);
  void presolve();
  void addSharedTerm(TNode t);
  EqualityStatus getEqualityStatus(TNode a, TNode b);
  void collectModelInfo( TheoryModel* m, bool fullModel );
  void shutdown() { }
  std::string identify() const { return std::string("TheoryDatatypes"); }
  /** debug print */
  void printModelDebug( const char* c );
private:
  /** add tester to equivalence class info */
  void addTester( Node t, EqcInfo* eqc, Node n );
  /** add selector to equivalence class info */
  void addSelector( Node s, EqcInfo* eqc, Node n, bool assertFacts = true );
  /** add constructor */
  void addConstructor( Node c, EqcInfo* eqc, Node n );
  /** merge the equivalence class info of t1 and t2 */
  void merge( Node t1, Node t2 );
  /** collapse selector, s is of the form sel( n ) where n = c */
  void collapseSelector( Node s, Node c );
  /** for checking if cycles exist */
  void checkCycles();
  Node searchForCycle( TNode n, TNode on,
                       std::map< TNode, bool >& visited,
                       std::vector< TNode >& explanation, bool firstTime = true );
  /** for checking whether two codatatype terms must be equal */
  void separateBisimilar( std::vector< Node >& part, std::vector< std::vector< Node > >& part_out,
                          std::vector< TNode >& exp,
                          std::map< Node, Node >& cn,
                          std::map< Node, std::map< Node, int > >& dni, int dniLvl, bool mkExp );
  /** build model */
  Node getCodatatypesValue( Node n, std::map< Node, Node >& eqc_cons, std::map< Node, Node >& eqc_mu, std::map< Node, Node >& vmap, std::vector< Node >& fv );
  /** collect terms */
  void collectTerms( Node n );
  /** get instantiate cons */
  Node getInstantiateCons( Node n, const Datatype& dt, int index, bool isActive );
  /** process new term that was created internally */
  void processNewTerm( Node n );
  /** check instantiate */
  void instantiate( EqcInfo* eqc, Node n );
  /** must specify model
    *  This returns true when the datatypes theory is expected to specify the constructor
    *  type for all equivalence classes.
    */
  bool mustSpecifyAssignment();
  /** must communicate fact */
  bool mustCommunicateFact( Node n, Node exp );
  /** check clash mod eq */
  bool checkClashModEq( TNode n1, TNode n2, std::vector< Node >& exp, std::vector< std::pair< TNode, TNode > >& deq_cand );
private:
  //equality queries
  bool hasTerm( TNode a );
  bool areEqual( TNode a, TNode b );
  bool areDisequal( TNode a, TNode b );
  TNode getRepresentative( TNode a );
public:
  /** get equality engine */
  eq::EqualityEngine* getEqualityEngine() { return &d_equalityEngine; }
};/* class TheoryDatatypes */

}/* CVC4::theory::datatypes namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__DATATYPES__THEORY_DATATYPES_H */
