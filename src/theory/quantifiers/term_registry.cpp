/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Term registry class.
 */

#include "theory/quantifiers/term_registry.h"

#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "options/smt_options.h"
#include "theory/quantifiers/entailment_check.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/fmf/first_order_model_fmc.h"
#include "theory/quantifiers/ho_term_database.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

TermRegistry::TermRegistry(Env& env,
                           QuantifiersState& qs,
                           QuantifiersRegistry& qr)
    : EnvObj(env),
      d_presolve(userContext(), true),
      d_presolveCache(userContext()),
      d_termEnum(new TermEnumeration),
      d_termPools(new TermPools(env, qs)),
      d_termDb(logicInfo().isHigherOrder() ? new HoTermDb(env, qs, qr)
                                           : new TermDb(env, qs, qr)),
      d_echeck(new EntailmentCheck(env, qs, *d_termDb.get())),
      d_sygusTdb(nullptr),
      d_qmodel(nullptr)
{
  if (options::sygus() || options::sygusInst())
  {
    // must be constructed here since it is required for datatypes finistInit
    d_sygusTdb.reset(new TermDbSygus(env, qs));
  }
  Trace("quant-engine-debug") << "Initialize quantifiers engine." << std::endl;
  Trace("quant-engine-debug")
      << "Initialize model, mbqi : " << options::mbqiMode() << std::endl;
}

void TermRegistry::finishInit(FirstOrderModel* fm,
                              QuantifiersInferenceManager* qim)
{
  d_qmodel = fm;
  d_termDb->finishInit(qim);
  if (d_sygusTdb.get())
  {
    d_sygusTdb->finishInit(qim);
  }
}

void TermRegistry::presolve()
{
  d_presolve = false;
  // add all terms to database
  if (options::incrementalSolving() && !options::termDbCd())
  {
    Trace("quant-engine-proc")
        << "Add presolve cache " << d_presolveCache.size() << std::endl;
    for (const Node& t : d_presolveCache)
    {
      addTerm(t);
    }
    Trace("quant-engine-proc") << "Done add presolve cache " << std::endl;
  }
}

void TermRegistry::addTerm(Node n, bool withinQuant)
{
  // don't add terms in quantifier bodies
  if (withinQuant && !options::registerQuantBodyTerms())
  {
    return;
  }
  if (options::incrementalSolving() && !options::termDbCd())
  {
    d_presolveCache.insert(n);
  }
  // only wait if we are doing incremental solving
  if (!d_presolve || !options::incrementalSolving() || options::termDbCd())
  {
    d_termDb->addTerm(n);
    if (d_sygusTdb.get() && options::sygusEvalUnfold())
    {
      d_sygusTdb->getEvalUnfold()->registerEvalTerm(n);
    }
  }
}

Node TermRegistry::getTermForType(TypeNode tn)
{
  if (tn.isClosedEnumerable())
  {
    return d_termEnum->getEnumerateTerm(tn, 0);
  }
  return d_termDb->getOrMakeTypeGroundTerm(tn);
}

void TermRegistry::declarePool(Node p, const std::vector<Node>& initValue)
{
  d_termPools->registerPool(p, initValue);
}

void TermRegistry::processInstantiation(Node q, const std::vector<Node>& terms)
{
  d_termPools->processInstantiation(q, terms);
}
void TermRegistry::processSkolemization(Node q,
                                        const std::vector<Node>& skolems)
{
  d_termPools->processSkolemization(q, skolems);
}

TermDb* TermRegistry::getTermDatabase() const { return d_termDb.get(); }

TermDbSygus* TermRegistry::getTermDatabaseSygus() const
{
  return d_sygusTdb.get();
}

EntailmentCheck* TermRegistry::getEntailmentCheck() const
{
  return d_echeck.get();
}

TermEnumeration* TermRegistry::getTermEnumeration() const
{
  return d_termEnum.get();
}

TermPools* TermRegistry::getTermPools() const { return d_termPools.get(); }

FirstOrderModel* TermRegistry::getModel() const { return d_qmodel; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5
