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


import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;


/**
 * AST node for taclet modifiers (like heuristics and
 * interactive). All nodes for taclet modifiers are instances of
 * subclasses of this class. See {@link #accept} and {@link
 * AstTacletModifierVisitor} for more information.
 *
 * @author Hubert Schmid
 */

public abstract class AstTacletModifier extends AstNode {

    public AstTacletModifier(Location location) {
        super(location);
    }


    /** This methods calls the corresponding method in visitor. */
    public abstract void accept(AstTacletModifierVisitor visitor) throws ParserException;

}
