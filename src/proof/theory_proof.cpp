/*********************                                                        */
/*! \file theory_proof.cpp
 ** \verbatim
 ** Original author: Liana Hadarean
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "proof/theory_proof.h"

using namespace CVC4;

TheoryProof::TheoryProof()
  : d_atomSet()
  , d_inputFormulas()
  , d_termDeclarations()
  , d_sortDeclarations()
  , d_declarationCache()
{}

void TheoryProof::addAtom(Expr atom) {
  d_atomSet.insert(atom); 
  Assert (atom.getKind() == kind::EQUAL);
  addDeclaration(atom[0]);
  addDeclaration(atom[1]); 
}

void TheoryProof::assertFormula(Expr formula) {
  d_inputFormulas.insert(formula);
  addDeclaration(formula); 
}

void TheoryProof::addDeclaration(Expr term) {
  if (d_declarationCache.count(term))
    return;
  
  Type type = term.getType();
  if (type.isSort())
    d_sortDeclarations.insert(type);
  if (term.getKind() == kind::APPLY_UF) {
    Expr function = term.getOperator();
    d_termDeclarations.insert(function);
  } else if (term.isVariable()) {
    Assert (type.isSort()); 
    d_termDeclarations.insert(term);
  }
  // recursively declare all other terms
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    addDeclaration(term[i]); 
  }
  d_declarationCache.insert(term); 
}

void LFSCTheoryProof::printTerm(Expr term, std::ostream& os) {
  if (term.isVariable()) {
    os << term; 
    return;
  }
  std::ostringstream paren; 
  Assert (term.getKind() == kind::APPLY_UF);
  Expr func = term.getOperator();
  os << "(apply _ _ " << func << " ";
  for (unsigned i = 0; i < term.getNumChildren(); ++i) {
    printTerm(term[i], os);
    if (i < term.getNumChildren() - 1) {
      os << "(apply _ _ " << func << " ";
      paren << ")"; 
    }
    os << ")" ; 
  }
  os << paren.str(); 
}

std::string toLFSCKind(Kind kind) {
  switch(kind) {
  case kind::OR : return "or";
  case kind::AND: return "and";
  case kind::XOR: return "xor";
  case kind::EQUAL: return "=";
  case kind::IMPLIES: return "impl";
  case kind::NOT: return "not";
  default:
    Unreachable(); 
  }
}

void LFSCTheoryProof::printFormula(Expr atom, std::ostream& os) {
  // should make this more general and overall sane
  Assert (atom.getType().isBoolean());
  Kind kind = atom.getKind(); 
  // this is the only predicate we have
  if (kind == kind::EQUAL) {
    os << "(";
    os <<"= ";
    os << atom[0].getType() <<" "; 
    printTerm(atom[0], os);
    os <<" "; 
    printTerm(atom[1], os);
    os <<")"; 
  } else if ( kind == kind::OR ||
              kind == kind::AND ||
              kind == kind::XOR ||
              kind == kind::IMPLIES ||
              kind == kind::NOT) {
    // print the boolean operators
    os << "(";
    os << toLFSCKind(kind);
    if (atom.getNumChildren() > 2) {
      std::ostringstream paren;
      os << " ";
      for (unsigned i =0; i < atom.getNumChildren(); ++i) {
        printFormula(atom[i], os);
        os << " ";
        if (i < atom.getNumChildren() - 2) {
          os << "("<< toLFSCKind(kind) << " "; 
          paren << ")"; 
        }
      }
      os << paren.str() <<")"; 
    } else {
      // this is for binary and unary operators 
      for (unsigned i = 0; i < atom.getNumChildren(); ++i) {
        os <<" ";
        printFormula(atom[i], os); 
      }
      os <<")"; 
    }
  } else {
    Assert (false); 
  }
}

void LFSCTheoryProof::printAssertions(std::ostream& os, std::ostream& paren) {
  unsigned counter = 0; 
  for (ExprSet::const_iterator it = d_inputFormulas.begin(); it != d_inputFormulas.end(); ++it) {
    os << "(% A" << counter++ << " (th_holds ";
    printFormula(*it,  os);
    os << ")\n";
    paren <<")"; 
  }
}

void LFSCTheoryProof::printDeclarations(std::ostream& os, std::ostream& paren) {
  // declaring the sorts
  for (SortSet::const_iterator it = d_sortDeclarations.begin(); it != d_sortDeclarations.end(); ++it) {
    os << "(% " << *it << " sort \n";
    paren << ")"; 
  }

  // declaring the terms
  for (ExprSet::const_iterator it = d_termDeclarations.begin(); it != d_termDeclarations.end(); ++it) {
    Expr term = *it;
    
    os << "(% " << term << " (term "; 
    paren <<")"; 

    Type type = term.getType();
    if (type.isFunction()) {
      std::ostringstream fparen; 
      FunctionType ftype = (FunctionType)type;
      std::vector<Type> args = ftype.getArgTypes();
      args.push_back(ftype.getRangeType()); 
      os << "(arrow "; 
      for (unsigned i = 0; i < args.size(); i++) {
        Type arg_type = args[i];
        Assert (arg_type.isSort());
        os << arg_type << " ";  
        if (i < args.size() - 2) {
          os << "(arrow ";
          fparen <<")"; 
        }
      }
      os << fparen.str() << "))\n"; 
    } else {
      Assert (term.isVariable());
      Assert (type.isSort());
      os << type << ")\n";
    }
  }
} 
