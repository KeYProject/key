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


/**
 *  Public.
 *  @author <TT>AutoDoc</TT>
 */

public class Public extends VisibilityModifier {


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     */
    public Public() {
	super();
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     *  May contain: Comments
     */
    public Public(de.uka.ilkd.key.util.ExtList children) {
	super(children);
    }

    /**
     *      Get symbol.
     *      @return the string.
     */
    protected String getSymbol() {
        return "public";
    }
}
