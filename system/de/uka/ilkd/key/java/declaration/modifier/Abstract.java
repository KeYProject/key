// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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
 *  Abstract.
 */

public class Abstract extends Modifier {

    /**
     *      Abstract.
     */
    public Abstract() {}


    /**
     *      Abstract.
     * @param children list of children. May contain: Comments
     */
    public Abstract(ExtList children) {
	super (children);
    }




    /**
     *      Get symbol.
     *      @return the string.
     */
    protected String getSymbol() {
        return "abstract";
    }
}
