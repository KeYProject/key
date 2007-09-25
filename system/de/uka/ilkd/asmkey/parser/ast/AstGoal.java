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
 * AST node for taclet goals. All nodes for taclet goals are instances
 * of subclasses of this class. See {@link #accept} and {@link
 * AstGoal} for more information.
 *
 * @author Hubert Schmid
 */

public abstract class AstGoal extends AstNode {

    public AstGoal(Location location) {
        super(location);
    }


    /** This methods calls the corresponding method in visitor. */
    public abstract void accept(AstGoalVisitor visitor) throws ParserException;

}
