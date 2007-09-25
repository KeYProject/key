// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;

import de.uka.ilkd.key.parser.ParserException;


/** Visitor for declarations.
 *
 * @see AstDeclaration
 * @author Hubert Schmid
 */

public interface AstDeclarationVisitor {

    /** Declaration of a new primitive sort. */
    void visitPrimitiveSort(boolean isGenericSort)
	throws ParserException;

    /** Declaration of a enumerated sort */
    void visitEnumeratedSort(Identifier[] consts)
	throws ParserException;

    /** Declaration of a schema variable. */
    void visitSchemaVariable(AstSchemaType type)
	throws ParserException;

    /** Declaration of a predicate symbol. */
    void visitPredicate(AstType[] args)
	throws ParserException;

    /** Declaration of a derived predicate symbol; at the first pass.
     * we do not parse the formula in the first pass, but only collect the identifiers
     * and check the sorst of the parameters.
     */
    void visitDerivedPredicateFirstPass(AstParameter[] params)
	throws ParserException;

    /**
     * Declaration of a derived predicate symbol; at the second pass.
     * we parse the formula.
     */
    void visitDerivedPredicateSecondPass(AstTerm formula)
	throws ParserException;

    /** Declaration of a function symbol. */
    void visitFunction(AstType[] args, AstType ret, boolean dynamic)
	throws ParserException;

    /** Declaration of a derived function symbol.
     * same comments as for the derived predicate.
     * @see #visitDerivedPredicateFirstPass(AstParameter[] params)
     */
    void visitDerivedFunctionFirstPass(AstParameter[] params,
			      AstType ret)
	throws ParserException;

    /** Declaration of a derived function symbol, at the second pass.
     */
    void visitDerivedFunctionSecondPass(AstTerm body)
	throws ParserException;

    /** Taclet declaration. */
    void visitTaclet(AstTaclet taclet)
	throws ParserException;
    
    /** Abstract ASM rules, used to prove PO with any assumption on rules used */
    void visitAbstractAsmRule() 
	throws ParserException;

    /** Named ASM rule (rule) declaration; at the first pass
     * same comments as for the derived predicates.
     * @see #visitDerivedPredicateFirstPass(AstParameter[] params)*/
    void visitNamedRuleFirstPass(AstParameter[] params)
	throws ParserException;

    /** Named ASM rule (rule) declaration; at the second pass */
    void visitNamedRuleSecondPass(AstAsmRule body)
	throws ParserException;

    /** Lemma declaration (that a proof may use) */
    void visitLemma(AstParameter[] params, AstTerm phi)
	throws ParserException;

    /** A Rule Set (used for strategies) */
    void visitRuleSet()
	throws ParserException;

    /** The name of a meta operator: the parser instancies
     * the correct metaoperator
     */
    void visitMetaOperator()
	throws ParserException;

}
