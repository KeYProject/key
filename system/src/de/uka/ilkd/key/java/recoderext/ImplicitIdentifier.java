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


package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;

/**
 * subclasses the recoder Identifier in order to allow fields with special
 * characters. For example, these are used to distinct between implicit and
 * customary class fields.
 */
public class ImplicitIdentifier extends Identifier {
    
    /**
     * 
     */
    private static final long serialVersionUID = -4226362019731704838L;

    public ImplicitIdentifier(String id) {
	super(id);
    }

    protected void setText(String text) {
	id = text.intern();
    }
    
    /**
     * Deep clone.
     * @return the object.
     */
    
    public ImplicitIdentifier deepClone() {
        return new ImplicitIdentifier(id);
    }
    
}
