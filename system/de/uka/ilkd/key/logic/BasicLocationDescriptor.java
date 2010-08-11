// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.sort.Sort;

public class BasicLocationDescriptor implements LocationDescriptor {
    
    private final static Term trueTerm = TermBuilder.DF.tt();
    private final Term fma;
    private final Term locTerm;
    
    
    public BasicLocationDescriptor(Term fma, Term locTerm) {
        assert fma != null && fma.sort() == Sort.FORMULA && locTerm != null;
        if (!(locTerm.op() instanceof Location)) {
            throw new IllegalArgumentException("Expected a location, but " + locTerm + 
                    " is a " + locTerm.op().getClass().getName());
        }
        this.fma = fma;
        this.locTerm = locTerm;
    }
    
    
    public BasicLocationDescriptor(Term locTerm) {
        this(trueTerm, locTerm);
    }
    
    
    public Term getFormula() {
        return fma;
    }
    
    
    public Term getLocTerm() {
        return locTerm;
    }    
    
    
    public boolean equals(Object o) {
        if(!(o instanceof BasicLocationDescriptor)) {
            return false;
        }       
        BasicLocationDescriptor ld = (BasicLocationDescriptor) o;
        return fma.equals(ld.fma) && locTerm.equals(ld.locTerm);
    }
    
    
    public int hashCode() {
        return fma.hashCode() + locTerm.hashCode();
    }
    
    
    public String toString() {
        return (fma.equals(trueTerm) 
                ? locTerm.toString() 
                : "\\if" + fma + "; " + locTerm);
    }
}
