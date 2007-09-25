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


/** Visitor for taclet goals.
 *
 * @see AstGoal
 * @author Hubert Schmid
 */

public interface AstGoalVisitor {

    /** Replace goal with a term. */
    void visitReplace(String name, AstTerm term,
                      AstSequent addSequent,
                      AstTacletDeclaration[] addRules)
	throws ParserException;

    /** Replace goal with a sequent. */
    void visitReplace(String name, AstSequent sequent,
                      AstSequent addSequent,
                      AstTacletDeclaration[] addRules)
	throws ParserException;

    /** Replace goal for elseif */
    void visitReplace(String name, AstSequent sequent)
	throws ParserException;

}
