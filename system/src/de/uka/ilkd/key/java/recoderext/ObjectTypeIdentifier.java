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

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Identifier;

public class ObjectTypeIdentifier extends Identifier {
    
    /**
     * 
     */
    private static final long serialVersionUID = -2181868786991278019L;

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