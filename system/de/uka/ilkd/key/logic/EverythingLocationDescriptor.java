// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;


public class EverythingLocationDescriptor implements LocationDescriptor {
    public static final EverythingLocationDescriptor INSTANCE 
            = new EverythingLocationDescriptor();
    
    public static final ImmutableSet<LocationDescriptor> INSTANCE_AS_SET
    	    = DefaultImmutableSet.<LocationDescriptor>nil().add(INSTANCE);
    
    private EverythingLocationDescriptor() {}
    
    public String toString() {
        return "*";
    }
}
