/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the command pattern on SolverEngines.
 *
 * Command objects are generated by the parser (typically) to implement the
 * commands in parsed input (see Parser::parseNextCommand()), or by client
 * code.
 */

#include "cvc5_public.h"

#ifndef CVC5__PARSER__COMMANDS_H
#define CVC5__PARSER__COMMANDS_H

#include <cvc5/cvc5.h>

#include <iosfwd>
#include <sstream>
#include <string>
#include <vector>

#include "options/language.h"

namespace cvc5 {

class Solver;
class Term;

namespace main {
class CommandExecutor;
}

namespace parser {

class CommandStatus;
class SymManager;

/**
 * Convert a symbolic expression to string. This method differs from
 * Term::toString in that it does not depend on the output language.
 *
 * @param sexpr the symbolic expression to convert
 * @return the symbolic expression as string
 */
std::string sexprToString(cvc5::Term sexpr) CVC5_EXPORT;

/**
 * Encapsulation of a command.
 *
 * Commands are constructed by the input parser and can be invoked on
 * the solver and symbol manager.
 */
class CVC5_EXPORT Cmd
{
  friend class main::CommandExecutor;

 public:
  Cmd();
  Cmd(const Cmd& cmd);

  virtual ~Cmd();

  /**
   * Invoke the command on the solver and symbol manager sm.
   */
  virtual void invoke(cvc5::Solver* solver, parser::SymManager* sm) = 0;
  /**
   * Same as above, and prints the result to output stream out.
   */
  virtual void invoke(cvc5::Solver* solver,
                      parser::SymManager* sm,
                      std::ostream& out);

  /**
   * @return A string representation of this result.
   */
  std::string toString() const;

  /**
   * Get the name for this command, e.g. "assert".
   *
   * @return The name of this command.
   */
  virtual std::string getCommandName() const = 0;

  /**
   * Either the command hasn't run yet, or it completed successfully
   * (CommandSuccess, not CommandUnsupported or CommandFailure).
   *
   * @return Whether the command was successfully invoked.
   */
  bool ok() const;

  /**
   * The command completed in a failure state (CommandFailure, not
   * CommandSuccess or CommandUnsupported).
   *
   * @return Whether the command failed.
   */
  bool fail() const;

  /**
   * The command was ran but was interrupted due to resource limiting.
   *
   * @return Whether the command was interrupted.
   */
  bool interrupted() const;

 protected:
  virtual void toStream(std::ostream& out) const = 0;
  /**
   * This field contains a command status if the command has been
   * invoked, or NULL if it has not.  This field is either a
   * dynamically-allocated pointer, or it's a pointer to the singleton
   * CommandSuccess instance.  Doing so is somewhat asymmetric, but
   * it avoids the need to dynamically allocate memory in the common
   * case of a successful command.
   */
  const CommandStatus* d_commandStatus;
  /**
   * Print the result of running the command. This method is only called if the
   * command ran successfully.
   */
  virtual void printResult(cvc5::Solver* solver, std::ostream& out) const;
  /**
   * Reset the given solver in-place (keep the object at the same memory
   * location).
   */
  static void resetSolver(cvc5::Solver* solver);

  // These methods rely on Command being a friend of classes in the API.
  // Subclasses of command should use these methods for conversions,
  // which is currently necessary for e.g. printing commands.
  /** Helper to convert a Term to an internal internal::Node */
  static internal::Node termToNode(const cvc5::Term& term);
  /** Helper to convert a vector of Terms to internal Nodes. */
  static std::vector<internal::Node> termVectorToNodes(
      const std::vector<cvc5::Term>& terms);
  /** Helper to convert a Sort to an internal internal::TypeNode */
  static internal::TypeNode sortToTypeNode(const cvc5::Sort& sort);
  /** Helper to convert a vector of Sorts to internal TypeNodes. */
  static std::vector<internal::TypeNode> sortVectorToTypeNodes(
      const std::vector<cvc5::Sort>& sorts);
  /** Helper to convert a Grammar to an internal internal::TypeNode */
  static internal::TypeNode grammarToTypeNode(cvc5::Grammar* grammar);
}; /* class Command */

/**
 * EmptyCommands are the residue of a command after the parser handles
 * them (and there's nothing left to do).
 */
class CVC5_EXPORT EmptyCommand : public Cmd
{
 public:
  EmptyCommand(std::string name = "");
  std::string getName() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  std::string d_name;
}; /* class EmptyCommand */

class CVC5_EXPORT EchoCommand : public Cmd
{
 public:
  EchoCommand(std::string output = "");

  std::string getOutput() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void invoke(cvc5::Solver* solver,
              parser::SymManager* sm,
              std::ostream& out) override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  std::string d_output;
}; /* class EchoCommand */

class CVC5_EXPORT AssertCommand : public Cmd
{
 protected:
  cvc5::Term d_term;

 public:
  AssertCommand(const cvc5::Term& t);

  cvc5::Term getTerm() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class AssertCommand */

class CVC5_EXPORT PushCommand : public Cmd
{
 public:
  PushCommand(uint32_t nscopes);

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 private:
  uint32_t d_nscopes;
}; /* class PushCommand */

class CVC5_EXPORT PopCommand : public Cmd
{
 public:
  PopCommand(uint32_t nscopes);

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 private:
  uint32_t d_nscopes;
}; /* class PopCommand */

class CVC5_EXPORT DeclarationDefinitionCommand : public Cmd
{
 protected:
  std::string d_symbol;
  /**
   * Bind the symbol of this command to the given term. Return false if the
   * binding was invalid. In this case, set command status to CommandFailure.
   */
  bool bindToTerm(parser::SymManager* sm, cvc5::Term t, bool doOverload);

 public:
  DeclarationDefinitionCommand(const std::string& id);

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override = 0;
  std::string getSymbol() const;
}; /* class DeclarationDefinitionCommand */

class CVC5_EXPORT DeclareFunctionCommand : public DeclarationDefinitionCommand
{
 protected:
  std::vector<Sort> d_argSorts;
  cvc5::Sort d_sort;

 public:
  DeclareFunctionCommand(const std::string& id,
                         const std::vector<Sort>& argSorts,
                         cvc5::Sort sort);
  std::vector<Sort> getArgSorts() const;
  cvc5::Sort getSort() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class DeclareFunctionCommand */

class CVC5_EXPORT DeclarePoolCommand : public DeclarationDefinitionCommand
{
 protected:
  cvc5::Sort d_sort;
  std::vector<cvc5::Term> d_initValue;

 public:
  DeclarePoolCommand(const std::string& id,
                     cvc5::Sort sort,
                     const std::vector<cvc5::Term>& initValue);
  cvc5::Sort getSort() const;
  const std::vector<cvc5::Term>& getInitialValue() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class DeclarePoolCommand */

class CVC5_EXPORT DeclareOracleFunCommand : public Cmd
{
 public:
  DeclareOracleFunCommand(const std::string& id,
                          const std::vector<Sort>& argSorts,
                          Sort sort);
  DeclareOracleFunCommand(const std::string& id,
                          const std::vector<Sort>& argSorts,
                          Sort sort,
                          const std::string& binName);
  const std::string& getIdentifier() const;
  std::vector<Sort> getArgSorts() const;
  Sort getSort() const;
  const std::string& getBinaryName() const;

  void invoke(Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The identifier */
  std::string d_id;
  /** Argument sorts */
  std::vector<Sort> d_argSorts;
  /** The return sort */
  Sort d_sort;
  /** The binary name, or "" if none is provided */
  std::string d_binName;
};

class CVC5_EXPORT DeclareSortCommand : public DeclarationDefinitionCommand
{
 protected:
  size_t d_arity;
 public:
  DeclareSortCommand(const std::string& id, size_t arity);

  size_t getArity() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class DeclareSortCommand */

class CVC5_EXPORT DefineSortCommand : public DeclarationDefinitionCommand
{
 protected:
  std::vector<cvc5::Sort> d_params;
  cvc5::Sort d_sort;

 public:
  DefineSortCommand(const std::string& id, cvc5::Sort sort);
  DefineSortCommand(const std::string& id,
                    const std::vector<cvc5::Sort>& params,
                    cvc5::Sort sort);

  const std::vector<cvc5::Sort>& getParameters() const;
  cvc5::Sort getSort() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class DefineSortCommand */

class CVC5_EXPORT DefineFunctionCommand : public DeclarationDefinitionCommand
{
 public:
  DefineFunctionCommand(const std::string& id,
                        cvc5::Sort sort,
                        cvc5::Term formula);
  DefineFunctionCommand(const std::string& id,
                        const std::vector<cvc5::Term>& formals,
                        cvc5::Sort sort,
                        cvc5::Term formula);

  const std::vector<cvc5::Term>& getFormals() const;
  cvc5::Sort getSort() const;
  cvc5::Term getFormula() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The formal arguments for the function we are defining */
  std::vector<cvc5::Term> d_formals;
  /** The co-domain sort of the function we are defining */
  cvc5::Sort d_sort;
  /** The formula corresponding to the body of the function we are defining */
  cvc5::Term d_formula;
}; /* class DefineFunctionCommand */

/**
 * The command when parsing define-fun-rec or define-funs-rec.
 * This command will assert a set of quantified formulas that specify
 * the (mutually recursive) function definitions provided to it.
 */
class CVC5_EXPORT DefineFunctionRecCommand : public Cmd
{
 public:
  DefineFunctionRecCommand(cvc5::Term func,
                           const std::vector<cvc5::Term>& formals,
                           cvc5::Term formula);
  DefineFunctionRecCommand(const std::vector<cvc5::Term>& funcs,
                           const std::vector<std::vector<cvc5::Term> >& formals,
                           const std::vector<cvc5::Term>& formula);

  const std::vector<cvc5::Term>& getFunctions() const;
  const std::vector<std::vector<cvc5::Term> >& getFormals() const;
  const std::vector<cvc5::Term>& getFormulas() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** functions we are defining */
  std::vector<cvc5::Term> d_funcs;
  /** formal arguments for each of the functions we are defining */
  std::vector<std::vector<cvc5::Term> > d_formals;
  /** formulas corresponding to the bodies of the functions we are defining */
  std::vector<cvc5::Term> d_formulas;
}; /* class DefineFunctionRecCommand */

/**
 * In separation logic inputs, which is an extension of smt2 inputs, this
 * corresponds to the command:
 *   (declare-heap (T U))
 * where T is the location sort and U is the data sort.
 */
class CVC5_EXPORT DeclareHeapCommand : public Cmd
{
 public:
  DeclareHeapCommand(cvc5::Sort locSort, cvc5::Sort dataSort);
  cvc5::Sort getLocationSort() const;
  cvc5::Sort getDataSort() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The location sort */
  cvc5::Sort d_locSort;
  /** The data sort */
  cvc5::Sort d_dataSort;
};

/**
 * The command when parsing check-sat.
 * This command will check satisfiability of the input formula.
 */
class CVC5_EXPORT CheckSatCommand : public Cmd
{
 public:
  CheckSatCommand();
  cvc5::Result getResult() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 private:
  cvc5::Result d_result;
}; /* class CheckSatCommand */

/**
 * The command when parsing check-sat-assuming.
 * This command will assume a set of formulas and check satisfiability of the
 * input formula under these assumptions.
 */
class CVC5_EXPORT CheckSatAssumingCommand : public Cmd
{
 public:
  CheckSatAssumingCommand(cvc5::Term term);
  CheckSatAssumingCommand(const std::vector<cvc5::Term>& terms);

  const std::vector<cvc5::Term>& getTerms() const;
  cvc5::Result getResult() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 private:
  std::vector<cvc5::Term> d_terms;
  cvc5::Result d_result;
}; /* class CheckSatAssumingCommand */

/* ------------------- sygus commands  ------------------ */

/** Declares a sygus universal variable */
class CVC5_EXPORT DeclareSygusVarCommand : public DeclarationDefinitionCommand
{
 public:
  DeclareSygusVarCommand(const std::string& id,
                         cvc5::Sort sort);
  /** returns the declared variable */
  cvc5::Term getVar() const;
  /** returns the declared variable's sort */
  cvc5::Sort getSort() const;
  /** invokes this command
   *
   * The declared sygus variable is communicated to the SMT engine in case a
   * synthesis conjecture is built later on.
   */
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  /** returns this command's name */
  std::string getCommandName() const override;
  /** prints this command */
  void toStream(std::ostream& out) const override;

 protected:
  /** the declared variable's sort */
  cvc5::Sort d_sort;
};

/** Declares a sygus function-to-synthesize
 *
 * This command is also used for the special case in which we are declaring an
 * invariant-to-synthesize
 */
class CVC5_EXPORT SynthFunCommand : public DeclarationDefinitionCommand
{
 public:
  SynthFunCommand(const std::string& id,
                  const std::vector<cvc5::Term>& vars,
                  cvc5::Sort sort,
                  cvc5::Grammar* g);
  /** returns the input variables of the function-to-synthesize */
  const std::vector<cvc5::Term>& getVars() const;
  /** returns the sygus sort of the function-to-synthesize */
  cvc5::Sort getSort() const;
  /** Get the sygus grammar given for the synth fun command */
  const cvc5::Grammar* getGrammar() const;

  /** invokes this command
   *
   * The declared function-to-synthesize is communicated to the SMT engine in
   * case a synthesis conjecture is built later on.
   */
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  /** returns this command's name */
  std::string getCommandName() const override;
  /** prints this command */
  void toStream(std::ostream& out) const override;

 protected:
  /** the input variables of the function-to-synthesize */
  std::vector<cvc5::Term> d_vars;
  /** sort of the function-to-synthesize */
  cvc5::Sort d_sort;
  /** optional grammar for the possible values of the function-to-sytnhesize */
  cvc5::Grammar* d_grammar;
};

/** Declares a sygus constraint */
class CVC5_EXPORT SygusConstraintCommand : public Cmd
{
 public:
  SygusConstraintCommand(const cvc5::Term& t, bool isAssume = false);
  /** returns the declared constraint */
  cvc5::Term getTerm() const;
  /** invokes this command
   *
   * The declared constraint is communicated to the SMT engine in case a
   * synthesis conjecture is built later on.
   */
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  /** returns this command's name */
  std::string getCommandName() const override;
  /** prints this command */
  void toStream(std::ostream& out) const override;

 protected:
  /** the declared constraint */
  cvc5::Term d_term;
  /** true if this is a sygus assumption */
  bool d_isAssume;
};

/** Declares a sygus invariant constraint
 *
 * Invarint constraints are declared in a somewhat implicit manner in the SyGuS
 * language: they are declared in terms of the previously declared
 * invariant-to-synthesize, precondition, transition relation and condition.
 *
 * The actual constraint must be built such that the invariant is not stronger
 * than the precondition, not weaker than the postcondition and inductive
 * w.r.t. the transition relation.
 */
class CVC5_EXPORT SygusInvConstraintCommand : public Cmd
{
 public:
  SygusInvConstraintCommand(const std::vector<cvc5::Term>& predicates);
  SygusInvConstraintCommand(const cvc5::Term& inv,
                            const cvc5::Term& pre,
                            const cvc5::Term& trans,
                            const cvc5::Term& post);
  /** returns the place holder predicates */
  const std::vector<cvc5::Term>& getPredicates() const;
  /** invokes this command
   *
   * The place holders are communicated to the SMT engine and the actual
   * invariant constraint is built, in case an actual synthesis conjecture is
   * built later on.
   */
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  /** returns this command's name */
  std::string getCommandName() const override;
  /** prints this command */
  void toStream(std::ostream& out) const override;

 protected:
  /** the place holder predicates with which to build the actual constraint
   * (i.e. the invariant, precondition, transition relation and postcondition)
   */
  std::vector<cvc5::Term> d_predicates;
};

/** Declares a synthesis conjecture */
class CVC5_EXPORT CheckSynthCommand : public Cmd
{
 public:
  CheckSynthCommand(bool isNext = false) : d_isNext(isNext){};
  /** returns the result of the check-synth call */
  cvc5::SynthResult getResult() const;
  /** prints the result of the check-synth-call */
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  /** invokes this command
   *
   * This invocation makes the SMT engine build a synthesis conjecture based on
   * previously declared information (such as universal variables,
   * functions-to-synthesize and so on), set up attributes to guide the solving,
   * and then perform a satisfiability check, whose result is stored in
   * d_result.
   */
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  /** returns this command's name */
  std::string getCommandName() const override;
  /** prints this command */
  void toStream(std::ostream& out) const override;

 protected:
  /** Whether this is a check-synth-next call */
  bool d_isNext;
  /** result of the check-synth call */
  cvc5::SynthResult d_result;
  /** string stream that stores the output of the solution */
  std::stringstream d_solution;
};


/** Find synth command */
class CVC5_EXPORT FindSynthCommand : public Cmd
{
 public:
  FindSynthCommand(modes::FindSynthTarget fst, cvc5::Grammar* g)
      : d_fst(fst), d_grammar(g){};
  /** returns the result of the find-synth call */
  Term getResult() const;
  /** prints the result of the find-synth call */
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  /** invokes this command
   */
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  /** returns this command's name */
  std::string getCommandName() const override;
  /** prints this command */
  void toStream(std::ostream& out) const override;

 protected:
  /** The target type */
  modes::FindSynthTarget d_fst;
  /** optional grammar for the possible values */
  cvc5::Grammar* d_grammar;
  /** result of the check-synth call */
  Term d_result;
};

/** Find synth next command */
class CVC5_EXPORT FindSynthNextCommand : public Cmd
{
 public:
  FindSynthNextCommand(){};
  /** returns the result of the find-synth call */
  Term getResult() const;
  /** prints the result of the find-synth call */
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  /** invokes this command
   */
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  /** returns this command's name */
  std::string getCommandName() const override;
  /** prints this command */
  void toStream(std::ostream& out) const override;

 protected:
  /** result of the check-synth call */
  Term d_result;
};

/* ------------------- sygus commands  ------------------ */

// this is TRANSFORM in the CVC presentation language
class CVC5_EXPORT SimplifyCommand : public Cmd
{
 protected:
  cvc5::Term d_term;
  cvc5::Term d_result;

 public:
  SimplifyCommand(cvc5::Term term);

  cvc5::Term getTerm() const;
  cvc5::Term getResult() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class SimplifyCommand */

class CVC5_EXPORT GetValueCommand : public Cmd
{
 protected:
  std::vector<cvc5::Term> d_terms;
  std::vector<cvc5::Term> d_result;

 public:
  GetValueCommand(cvc5::Term term);
  GetValueCommand(const std::vector<cvc5::Term>& terms);

  const std::vector<cvc5::Term>& getTerms() const;
  const std::vector<cvc5::Term>& getResult() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class GetValueCommand */

class CVC5_EXPORT GetAssignmentCommand : public Cmd
{
 protected:
  cvc5::Term d_result;

 public:
  GetAssignmentCommand();

  cvc5::Term getResult() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class GetAssignmentCommand */

class CVC5_EXPORT GetModelCommand : public Cmd
{
 public:
  GetModelCommand();
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** Result of printing the model */
  std::string d_result;
}; /* class GetModelCommand */

/** The command to block models. */
class CVC5_EXPORT BlockModelCommand : public Cmd
{
 public:
  BlockModelCommand(modes::BlockModelsMode mode);

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 private:
  /** The mode to use for blocking. */
  modes::BlockModelsMode d_mode;
}; /* class BlockModelCommand */

/** The command to block model values. */
class CVC5_EXPORT BlockModelValuesCommand : public Cmd
{
 public:
  BlockModelValuesCommand(const std::vector<cvc5::Term>& terms);

  const std::vector<cvc5::Term>& getTerms() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The terms we are blocking */
  std::vector<cvc5::Term> d_terms;
}; /* class BlockModelValuesCommand */

class CVC5_EXPORT GetProofCommand : public Cmd
{
 public:
  GetProofCommand(modes::ProofComponent c = modes::ProofComponent::FULL);

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;

  void printResult(cvc5::Solver* solver, std::ostream& out) const override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 private:
  /** the result of the getProof call */
  std::string d_result;
  /** the requested proof component */
  modes::ProofComponent d_component;
}; /* class GetProofCommand */

class CVC5_EXPORT GetInstantiationsCommand : public Cmd
{
 public:
  GetInstantiationsCommand();

  static bool isEnabled(cvc5::Solver* solver, const cvc5::Result& res);
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  cvc5::Solver* d_solver;
}; /* class GetInstantiationsCommand */

/** The command (get-interpolant s B (G)?)
 *
 * This command asks for an interpolant from the current set of assertions and
 * conjecture (goal) B.
 *
 * The symbol s is the name for the interpolation predicate. If we successfully
 * find a predicate P, then the output response of this command is: (define-fun
 * s () Bool P)
 */
class CVC5_EXPORT GetInterpolantCommand : public Cmd
{
 public:
  GetInterpolantCommand(const std::string& name, Term conj);
  /** The argument g is the grammar of the interpolation query */
  GetInterpolantCommand(const std::string& name, Term conj, Grammar* g);

  /** Get the conjecture of the interpolation query */
  cvc5::Term getConjecture() const;
  /** Get the sygus grammar given for the interpolation query */
  const cvc5::Grammar* getGrammar() const;
  /** Get the result of the query, which is the solution to the interpolation
   * query. */
  cvc5::Term getResult() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The name of the interpolation predicate */
  std::string d_name;
  /** The conjecture of the interpolation query */
  cvc5::Term d_conj;
  /** The (optional) grammar of the interpolation query */
  cvc5::Grammar* d_sygus_grammar;
  /** the return expression of the command */
  cvc5::Term d_result;
}; /* class GetInterpolCommand */

/** The command (get-interpolant-next) */
class CVC5_EXPORT GetInterpolantNextCommand : public Cmd
{
 public:
  GetInterpolantNextCommand();
  /**
   * Get the result of the query, which is the solution to the interpolation
   * query.
   */
  cvc5::Term getResult() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The name of the interpolation predicate */
  std::string d_name;
  /** the return expression of the command */
  cvc5::Term d_result;
};

/** The command (get-abduct s B (G)?)
 *
 * This command asks for an abduct from the current set of assertions and
 * conjecture (goal) given by the argument B.
 *
 * The symbol s is the name for the abduction predicate. If we successfully
 * find a predicate P, then the output response of this command is:
 *   (define-fun s () Bool P)
 *
 * A grammar G can be optionally provided to indicate the syntactic restrictions
 * on the possible solutions returned.
 */
class CVC5_EXPORT GetAbductCommand : public Cmd
{
 public:
  GetAbductCommand(const std::string& name, cvc5::Term conj);
  GetAbductCommand(const std::string& name, cvc5::Term conj, cvc5::Grammar* g);

  /** Get the conjecture of the abduction query */
  cvc5::Term getConjecture() const;
  /** Get the grammar given for the abduction query */
  const cvc5::Grammar* getGrammar() const;
  /** Get the name of the abduction predicate for the abduction query */
  std::string getAbductName() const;
  /** Get the result of the query, which is the solution to the abduction query.
   */
  cvc5::Term getResult() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The name of the abduction predicate */
  std::string d_name;
  /** The conjecture of the abduction query */
  cvc5::Term d_conj;
  /** The (optional) grammar of the abduction query */
  cvc5::Grammar* d_sygus_grammar;
  /** the return expression of the command */
  cvc5::Term d_result;
}; /* class GetAbductCommand */

/** The command (get-abduct-next) */
class CVC5_EXPORT GetAbductNextCommand : public Cmd
{
 public:
  GetAbductNextCommand();
  /**
   * Get the result of the query, which is the solution to the abduction query.
   */
  cvc5::Term getResult() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The name of the abduction predicate */
  std::string d_name;
  /** the return expression of the command */
  cvc5::Term d_result;
};

class CVC5_EXPORT GetQuantifierEliminationCommand : public Cmd
{
 protected:
  cvc5::Term d_term;
  bool d_doFull;
  cvc5::Term d_result;

 public:
  GetQuantifierEliminationCommand();
  GetQuantifierEliminationCommand(const cvc5::Term& term, bool doFull);

  cvc5::Term getTerm() const;
  bool getDoFull() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  cvc5::Term getResult() const;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class GetQuantifierEliminationCommand */

class CVC5_EXPORT GetUnsatAssumptionsCommand : public Cmd
{
 public:
  GetUnsatAssumptionsCommand();
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::vector<cvc5::Term> getResult() const;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  std::vector<cvc5::Term> d_result;
}; /* class GetUnsatAssumptionsCommand */

class CVC5_EXPORT GetUnsatCoreCommand : public Cmd
{
 public:
  GetUnsatCoreCommand();
  const std::vector<cvc5::Term>& getUnsatCore() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The solver we were invoked with */
  cvc5::Solver* d_solver;
  /** The symbol manager we were invoked with */
  parser::SymManager* d_sm;
  /** the result of the unsat core call */
  std::vector<cvc5::Term> d_result;
}; /* class GetUnsatCoreCommand */

class CVC5_EXPORT GetUnsatCoreLemmasCommand : public Cmd
{
 public:
  GetUnsatCoreLemmasCommand();
  const std::vector<cvc5::Term>& getUnsatCoreLemmas() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The solver we were invoked with */
  cvc5::Solver* d_solver;
  /** the result of the unsat core call */
  std::vector<cvc5::Term> d_result;
}; /* class GetUnsatCoreLemmasCommand */

class CVC5_EXPORT GetDifficultyCommand : public Cmd
{
 public:
  GetDifficultyCommand();
  const std::map<cvc5::Term, cvc5::Term>& getDifficultyMap() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The symbol manager we were invoked with */
  parser::SymManager* d_sm;
  /** the result of the get difficulty call */
  std::map<cvc5::Term, cvc5::Term> d_result;
};

class CVC5_EXPORT GetTimeoutCoreCommand : public Cmd
{
 public:
  GetTimeoutCoreCommand();
  cvc5::Result getResult() const;
  const std::vector<cvc5::Term>& getTimeoutCore() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** The solver we were invoked with */
  cvc5::Solver* d_solver;
  /** The symbol manager we were invoked with */
  parser::SymManager* d_sm;
  /** the result of the timeout core call */
  std::pair<cvc5::Result, std::vector<cvc5::Term>> d_result;
};

class CVC5_EXPORT GetLearnedLiteralsCommand : public Cmd
{
 public:
  GetLearnedLiteralsCommand(modes::LearnedLitType t);
  const std::vector<cvc5::Term>& getLearnedLiterals() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;

  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;

 protected:
  /** the result of the get learned literals call */
  std::vector<cvc5::Term> d_result;
  /** The type of learned literals to get */
  modes::LearnedLitType d_type;
};

class CVC5_EXPORT GetAssertionsCommand : public Cmd
{
 protected:
  std::string d_result;

 public:
  GetAssertionsCommand();

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getResult() const;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class GetAssertionsCommand */

class CVC5_EXPORT SetBenchmarkLogicCommand : public Cmd
{
 protected:
  std::string d_logic;

 public:
  SetBenchmarkLogicCommand(std::string logic);

  std::string getLogic() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class SetBenchmarkLogicCommand */

class CVC5_EXPORT SetInfoCommand : public Cmd
{
 protected:
  std::string d_flag;
  std::string d_value;

 public:
  SetInfoCommand(const std::string& flag, const std::string& value);

  const std::string& getFlag() const;
  const std::string& getValue() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class SetInfoCommand */

class CVC5_EXPORT GetInfoCommand : public Cmd
{
 protected:
  std::string d_flag;
  std::string d_result;

 public:
  GetInfoCommand(std::string flag);

  std::string getFlag() const;
  std::string getResult() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class GetInfoCommand */

class CVC5_EXPORT SetOptionCommand : public Cmd
{
 protected:
  std::string d_flag;
  std::string d_value;

 public:
  SetOptionCommand(const std::string& flag, const std::string& value);

  const std::string& getFlag() const;
  const std::string& getValue() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class SetOptionCommand */

class CVC5_EXPORT GetOptionCommand : public Cmd
{
 protected:
  std::string d_flag;
  std::string d_result;

 public:
  GetOptionCommand(std::string flag);

  std::string getFlag() const;
  std::string getResult() const;

  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  void printResult(cvc5::Solver* solver, std::ostream& out) const override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class GetOptionCommand */

class CVC5_EXPORT DatatypeDeclarationCommand : public Cmd
{
 private:
  std::vector<cvc5::Sort> d_datatypes;

 public:
  DatatypeDeclarationCommand(const cvc5::Sort& datatype);

  DatatypeDeclarationCommand(const std::vector<cvc5::Sort>& datatypes);
  const std::vector<cvc5::Sort>& getDatatypes() const;
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class DatatypeDeclarationCommand */

class CVC5_EXPORT ResetCommand : public Cmd
{
 public:
  ResetCommand() {}
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class ResetCommand */

class CVC5_EXPORT ResetAssertionsCommand : public Cmd
{
 public:
  ResetAssertionsCommand() {}
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class ResetAssertionsCommand */

class CVC5_EXPORT QuitCommand : public Cmd
{
 public:
  QuitCommand() {}
  void invoke(cvc5::Solver* solver, parser::SymManager* sm) override;
  std::string getCommandName() const override;
  void toStream(std::ostream& out) const override;
}; /* class QuitCommand */

}  // namespace parser
}  // namespace cvc5

#endif /* CVC5__PARSER__COMMAND_H */
