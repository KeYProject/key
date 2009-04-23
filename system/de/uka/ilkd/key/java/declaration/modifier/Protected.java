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

import de.uka.ilkd.key.util.ExtList;

/**
 *  Protected.
 *  @author <TT>AutoDoc</TT>
 */

public class Protected extends VisibilityModifier {

    /**
 *      Protected.
     */

    public Protected() {}

    /**
 *      Protected.
     * @param children list of children. May contain: Comments
     */

    public Protected(ExtList children) {
	super(children);
    }


    /**
 *      Get symbol.
 *      @return the string.
     */

    protected String getSymbol() {
        return "protected";
    }
}
