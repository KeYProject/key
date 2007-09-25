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


/** Visitor for taclet variable conditions.
 *
 * @see AstCondition
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public interface AstConditionVisitor {

    /** Equality of top level operators. */
    void visitOperatorEquals(boolean equal, Identifier v, Identifier w) throws ParserException;

    /** Variable not free in term. */
    void visitNotFreeIn(Identifier v, Identifier w) throws ParserException;

    /** Pure term. */
    void visitPure(Identifier v) throws ParserException;

    /** Static term. */
    void visitStatic(Identifier v) throws ParserException;

    /** Term with static arguments. */
    void visitStaticArgs(Identifier v) throws ParserException;

    /** Term with dynamic top level operator (function symbol). */
    void visitDynamic(Identifier v) throws ParserException;

    /** Formula with predicate top level operator */
    void visitAtomic(Identifier v) throws ParserException;

    /** Top level operator is an asm named rule call. */
    void visitDerived(Identifier v) throws ParserException;

    /** Skolem symbol with meta variables. */
    void visitSkolem(Identifier v, Identifier w) throws ParserException;

    /** May or may not update a dynamic function. static analysis */
    void visitMayUpdate(boolean may, Identifier r, Identifier f) throws ParserException;

    /** May or may not access a dynamic function. static analysis */
    void visitMayAccess(boolean may, Identifier t, Identifier f) throws ParserException;
}
