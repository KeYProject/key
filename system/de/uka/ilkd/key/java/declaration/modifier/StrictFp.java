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
import de.uka.ilkd.key.util.ExtList;


/**
 *  Strict fp.
 *  @author <TT>AutoDoc</TT>
 */

public class StrictFp extends Modifier {

    /**
 *      Strict fp.
     */

    public StrictFp() {}

    /**
     * Strict fp.    
     * @param children the children of this AST element as KeY classes.
     *  May contain: Comments
     */

    public StrictFp(ExtList children) {
	super(children);
    }


    /**
 *      Get symbol.
 *      @return the string.
     */

    protected String getSymbol() {
        return "strictfp";
    }
}
