// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;

/**
 *  The JML modifier model
 */

public class Model extends Modifier {

    /**
     *  Model
     */
    public Model() {}


    /**
     *  Model.
     * @param children list of children. May contain: Comments
     */
    public Model(de.uka.ilkd.key.util.ExtList children) {
	super (children);
    }




    /**
     *      Get symbol.
     *      @return the string.
     */
    protected String getSymbol() {
        return "model";
    }
}
