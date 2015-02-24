// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.declaration.modifier;


import de.uka.ilkd.key.java.declaration.Modifier;

/**
 *  Final.
 *  @author <TT>AutoDoc</TT>
 */

public class Final extends Modifier {

    /**
     *      Final.
     */

    public Final() {}

    /**
     *      Abstract.
     * @param children list of children. May contain: Comments
     */
    public Final(de.uka.ilkd.key.util.ExtList children) {
	super (children);
    }
 
    /**
     *      Get symbol.
     *      @return the string.
     */
    protected String getSymbol() {
        return "final";
    }
}