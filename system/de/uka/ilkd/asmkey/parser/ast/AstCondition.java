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


/**
 * AST node for taclet variable conditions (like pure, static,
 * etc). All nodes for taclet variable conditions are instances of
 * subclasses of this class. See {@link #accept} and {@link
 * AstConditionVisitor} for more information.
 *
 * @author Hubert Schmid
 */

public abstract class AstCondition {

    /** This methods calls the corresponding method in visitor. */
    public abstract void accept(AstConditionVisitor visitor) throws ParserException;

}

