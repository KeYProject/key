// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.speclang.translation;

/**
 * This class represents a specific type of a collection (such as the ocl's set,
 * bag or sequence)
 * 
 */
public class SLCollectionType {

    public static final SLCollectionType SET = new SLCollectionType("Set");
    public static final SLCollectionType BAG = new SLCollectionType("Bag");
    public static final SLCollectionType SEQUENCE = new SLCollectionType("Sequence");
    
    
    private final String name;
    
    public SLCollectionType(String name) {
        this.name = name;
    }
    
    public String getName() {
        return this.name;
    }
    
    public boolean equals(Object t) {
        if (t instanceof SLCollectionType) {
            return this.name.equals(((SLCollectionType) t).getName());
        }
        return false;
    }
    
    public int hashCode() {
        return 37*19 + this.name.hashCode();
    }
}
