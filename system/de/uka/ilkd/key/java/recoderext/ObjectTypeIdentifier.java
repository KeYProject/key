// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;

public class ObjectTypeIdentifier extends Identifier {
    
    public ObjectTypeIdentifier(String id) {
        super(id);
    }

    protected void setText(String text) {
        id = text.intern();
    }
    
    /**
     * Deep clone.
     * @return the object.
     */
    
    public ObjectTypeIdentifier deepClone() {
        return new ObjectTypeIdentifier(id);
    }
    
}
