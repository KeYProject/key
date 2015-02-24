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
    
    @Override
    public int compareTo(VisibilityModifier arg0) {
        if (arg0 instanceof Private) return -3;
        if (arg0 == null) return -2;
        if (arg0 instanceof Protected) return -1;
        if (arg0 instanceof Public) return 0;
        assert false;
        return 0;
    }
}