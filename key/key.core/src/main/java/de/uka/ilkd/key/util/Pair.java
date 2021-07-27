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

import static de.uka.ilkd.key.util.MiscTools.equalsOrNull;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

public class Pair<T1, T2> {    
    public final T1 first;
    public final T2 second;


    public Pair(T1 first, T2 second) { 
        this.first = first;
        this.second = second;   
    }


    public String toString() { 
        return "(" + first + ", " + second + ")"; 
    }


    public boolean equals(Object o) {
        if(!(o instanceof Pair<?, ?>)) {
            return false;
        } 
        Pair<?, ?> p = (Pair<?, ?>) o;
        return equalsOrNull(first, p.first)
                        && equalsOrNull(second, p.second);
    }


    public int hashCode() {
        int res = 0;
        if (first != null) res += first.hashCode();
        if (second != null) res += second.hashCode();
        return res;
    }
    
    ///////////////////////////////////////////////////////////
    // convenience methods to operate on collections of pairs
    
    /**
     * Convert a collection of pairs into a map.
     * @throws IllegalArgumentException if it contains duplicate first entries
     */
    public static <S,T> Map<S,T> toMap (Collection<Pair<S,T>> pairs){
        Map<S,T> res = new java.util.LinkedHashMap<S,T>();
        for (Pair<S,T> p: pairs){
            if (res.containsKey(p.first))
                throw new IllegalArgumentException("Cannot covert "+pairs+" into a map; it contains duplicate first entries.");
            res.put(p.first, p.second);
        }
        return res;
    }
    
    /**
     * Returns the set of first entries from a collection of pairs.
     */
    public static <S,T> Set<S> getFirstSet (Collection<Pair<S,T>> pairs){
        Set<S> res = new java.util.HashSet<S>();
        for (Pair<S,T> p: pairs) {
            res.add(p.first);
        }
        return res;
    }
    
    /**
     * Returns the set of second entries from a collection of pairs.
     */
    public static <S,T> Set<T> getSecondSet (Collection<Pair<S,T>> pairs){
        Set<T> res = new java.util.HashSet<T>();
        for (Pair<S,T> p: pairs) {
            res.add(p.second);
        }
        return res;
    }
}