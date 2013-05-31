// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.java.declaration.modifier;


/**
 *  Private.
 *  @author <TT>AutoDoc</TT>
 */

public class Private extends VisibilityModifier {

    /**
     *      Private.
     */

    public Private() {}

    /**
     *      Private
     * @param children list of children. May contain: Comments
     */
    public Private(de.uka.ilkd.key.util.ExtList children) {
	super (children);
    }


    /**
     *      Get symbol.
     *      @return the string.
     */
    protected String getSymbol() {
        return "private";
    }

    @Override
    public int compareTo(VisibilityModifier arg0) {
        if (arg0 instanceof Private) return 0;
        if (arg0 == null) return 1;
        if (arg0 instanceof Protected) return 2;
        if (arg0 instanceof Public) return 3;
        assert false;
        return 0;
    }
}
