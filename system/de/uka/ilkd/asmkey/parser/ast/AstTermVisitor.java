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
import de.uka.ilkd.asmkey.parser.tree.ParsingStack;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;


/** Vistor for ASM terms.
 *
 * @see AstTerm
 * @author Hubert Schmid
 * @author Stanislas Nanchen  
 */

public interface AstTermVisitor {

    /* --- Terms of first order logic --- */

    /** Operator term: <tt>op(terms)</tt>. */
    Object visitOperatorTerm(ParsingStack closure, AstOperator op, AstTerm[] terms, Location location)
	throws ParserException;

    /** Big Operator term: <tt>And(f) phi</tt>. */
    Object visitBigTerm(ParsingStack closure, AstOperator op,
			Identifier sort, Identifier func, Identifier var, AstTerm formula)
	throws ParserException;

    /** Quantifier term: <tt>q var:sort. term</tt>. If sort is null,
     * then var is a schema variable. */
    Object visitQuantifierTerm(ParsingStack closure,
			       AstQuantifier q,
			       Identifier var, Identifier sort, AstTerm term, Location location)
	throws ParserException;

    /** Funtion term: <tt>id(terms)</tt>. */
    Object visitFunctionTerm(ParsingStack closure, Identifier id, AstTerm[] terms, Location location)
	throws ParserException;

    /** Substitution term: <tt>{var:sort = subst} term</tt>. If sort
     * is null, then var is a schema variable. */
    Object visitSubstitutionTerm(ParsingStack closure, Identifier var, Identifier sort,
				 AstTerm subst, AstTerm term, boolean waryEx, boolean waryAll,
				 Location location)
	throws ParserException;

    /** functions in formulas */
    Object visitFunctionTerm(ParsingStack closure, Identifier id, AstTerm func, AstTerm form,
			     Location location)
	throws ParserException;

    /** Term abbreviation. */
    Object visitAbbreviationTerm(ParsingStack closure, Identifier name, Location location)
	throws ParserException;

    /* --- Sequences and sets --- */

    //Object visitSetTerm (ParsingStack closure, AstTerm[] elems);

    Object visitSequenceTerm (ParsingStack closure,
			      Identifier basesort, AstTerm[] elems,
			      AstTerm tail, Location seqLoc)
	throws ParserException;

    /* --- Terms of dynamic logic --- */

    /** Term with modal box operator: <tt>[rule] term</tt>. */
    Object visitBox(ParsingStack closure, AstAsmRule rule, AstTerm term, AstTerm step,
		    Location location)
	throws ParserException;

    /** Term with modal diamond operator: <tt>&lt;rule&gt;
     * term</tt>. */
    Object visitDiamond(ParsingStack closure, AstAsmRule rule, AstTerm term, AstTerm step,
			Location location)
	throws ParserException;

    /* asm rules */

    /** Sequential ASM rule: <tt>rule1 ; rule2</tt>. */
    Object visitSeq(ParsingStack closure, AstAsmRule rule1, AstAsmRule rule2, Location location)
	throws ParserException;

    /** Parallel ASM rule: <tt>rule1 rule2</tt>. */
    Object visitPar(ParsingStack closure, AstAsmRule rule1, AstAsmRule rule2, Location location)
	throws ParserException;

    /** Skip ASM rule: <tt>skip</tt>. */
    Object visitSkip(ParsingStack closure, Location location)
	throws ParserException;

    /** Update ASM rule: <tt>lhs := rhs</tt>. */
    Object visitAssign(ParsingStack closure, AstTerm lhs, AstTerm rhs, Location location)
	throws ParserException;

    /** Call named ASM rule: <tt>id(terms)</tt>. */
    Object visitCall(ParsingStack closure, Identifier id, AstTerm[] terms, Location location)
	throws ParserException;

    /** If ASM rule: <tt>if formula then thenRule else
     * elseRule</tt>. */
    Object visitIf(ParsingStack closure, AstTerm formula, AstAsmRule thenRule, AstAsmRule elseRule,
		   Location location)
	throws ParserException;

    /** The conditional AsmRule, kind of else if
     */
    Object visitCond(ParsingStack closure,
		     AstTerm[] formulas, AstAsmRule[] rules, AstAsmRule otherwiseRule,
		     Location location)
	throws ParserException;

    /** Let ASM rule: <tt>let var:sort := term in rule</tt>. */
    Object visitLet(ParsingStack closure, Identifier var, Identifier sort,
		    AstTerm term, AstAsmRule rule, Location location)
	throws ParserException;

    /** Forall ASM rule: <tt>forall var:sort with formula do
     * rule</tt>. */
    Object visitForall(ParsingStack closure, Identifier var, Identifier sort,
		       AstTerm formula, AstAsmRule rule, Location location)
	throws ParserException;

    /** Try ASM rule: <tt>try tryRule else elseRule</tt>. */
    Object visitTry(ParsingStack closure, AstAsmRule tryRule, AstAsmRule elseRule,
		    Location location)
	throws ParserException;

    /** Variable for ASM rule: <tt>var</tt>. */
    Object visitAsmVariable(ParsingStack closure, Identifier var, Location location)
	throws ParserException;

    /** Substitution for ASM rule: <tt>{var:sort = subst}
     * term</tt>. */
    Object visitSubstitution(ParsingStack closure, Identifier var,
			     Identifier sort, AstTerm subst, AstAsmRule rule, Location location)
	throws ParserException;

    /** Metaoperator for ASM rule: <tt>id(rule)</tt>. The Metaoperator
     * has only one argument, an ASM rule. */
    Object visitMeta(ParsingStack closure, Identifier id, AstAsmRule rule, Location location)
	throws ParserException;
}
