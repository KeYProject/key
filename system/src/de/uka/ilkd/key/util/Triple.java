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

package de.uka.ilkd.key.util;


public class Triple<T1, T2, T3> {    
    public final T1 first;
    public final T2 second;
    public final T3 third;

    
    public Triple(T1 first, T2 second, T3 third) { 
        this.first  = first;
        this.second = second;   
        this.third  = third;
    }


    public String toString() { 
	return "(" + first + ", " + second + ", " + third + ")"; 
    }
    

    public boolean equals(Object o) {
        if(!(o instanceof Triple<?, ?, ?>)) {
            return false;
        } 
        Triple<?, ?, ?> p = (Triple<?, ?, ?>) o;
        return (first == null ? p.first == null : first.equals(p.first))
        && (second == null ? p.second == null : second.equals(p.second))
        && (third == null ? p.third == null : third.equals(p.third));
    }
    
    
    public int hashCode() {
        return 666*first.hashCode() + 42*second.hashCode() + 23*third.hashCode();
    }
}