// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.util.ExtList;


/**
 *  Visibility modifier.
 *  @author <TT>AutoDoc</TT>
 */

public abstract class VisibilityModifier 
    extends Modifier {

    public VisibilityModifier() {
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *  May contain: Comments
     */
    public VisibilityModifier(ExtList children) {
	super(children);
    }


}
