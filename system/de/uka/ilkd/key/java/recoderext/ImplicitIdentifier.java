// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2004 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;

/**
 * subclasses the recoder Identifier in order to allow fields with special
 * characters. For example, these are used to distinct between implicit and
 * customary class fields.
 */
public class ImplicitIdentifier extends Identifier {
    
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
    
    public Object deepClone() {
        return new ImplicitIdentifier(id);
    }
    
}
