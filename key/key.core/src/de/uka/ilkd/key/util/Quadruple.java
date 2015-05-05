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


public class Quadruple<T1, T2, T3, T4> {    
    public final T1 first;
    public final T2 second;
    public final T3 third;
    public final T4 fourth;

    
    public Quadruple(T1 first, T2 second, T3 third, T4 fourth) { 
        this.first  = first;
        this.second = second;
        this.third  = third;
        this.fourth  = fourth;
    }


    public String toString() { 
        return "(" + first + ", " + second + ", " + third + ", " + fourth + ")"; 
    }
    

    public boolean equals(Object o) {
        if(!(o instanceof Quadruple<?, ?, ?, ?>)) {
            return false;
        } 
        Quadruple<?, ?, ?, ?> p = (Quadruple<?, ?, ?, ?>) o;
        return (first == null ? p.first == null : first.equals(p.first))
        && (second == null ? p.second == null : second.equals(p.second))
        && (third == null ? p.third == null : third.equals(p.third))
        && (fourth == null ? p.fourth == null : fourth.equals(p.fourth));
    }
    
    
    public int hashCode() {
        int res = 0;
        if (first != null) res += 666*first.hashCode();
        if (second != null) res += 42*second.hashCode();
        if (third != null) res += 23*third.hashCode();
        if (fourth != null) res += 37*fourth.hashCode();
        return res;
    }
}