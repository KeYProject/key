// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.java.declaration.modifier;

import de.uka.ilkd.key.java.declaration.Modifier;


/**
 *  The JML modifier "model".
 */
public class Model extends Modifier {

    public Model() {}


    public Model(de.uka.ilkd.key.util.ExtList children) {
	super (children);
    }


    protected String getSymbol() {
        return "model";
    }
}
