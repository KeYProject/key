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

/** Visitor for taclet modifiers.
 *
 * @see AstTacletModifier
 * @author Hubert Schmid
 */

public interface AstTacletModifierVisitor {

    /** Heuristics. List of the heuristics, that should use this
     * taclet. */
    void visitHeuristics(Identifier[] heuristic) throws ParserException;

    /** Non interactive. */
    void visitNonInteractive() throws ParserException;

    /** Display name modifier. */
    void visitDisplayName(String displayName) throws ParserException;

    /** Help text modifier. */
    void visitHelpText(String helpText) throws ParserException;

    /** Same Update Level */
    void visitSameUpdateLevel() throws ParserException;

    /** In Sequent State */
    void visitInSequentState() throws ParserException;
}
