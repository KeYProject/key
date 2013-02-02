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

package de.uka.ilkd.key.java;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

/** 
 * This class is used for the equals modulo renaming method in
 * SourceElement. The purpose of this class is to abstract from
 * names. Therefore it represents a mapping o1 x o2 -> abstractName
 * where o1, o2 are of the same type (Label or ProgramVariable). The
 * objectif is that the comparing method uses this new name for o1 and
 * o2 instead of their real name. For this comparision a method is
 * offered so that the assigned name is not given outside.
 */
public class NameAbstractionTable {

    /**
     * The order in which symbols are declared in the two terms or programs that
     * are compared. The latest declaration of a symbol will be the first
     * matching entry in the list
     */
    private List<SourceElement> declarations0 = null, declarations1 = null;
    
    /** 
     * adds the given two elements to the table
     * @param pe1 SourceElement to be added
     * @param pe2 SourceElement to be added     
     */
    public void add(SourceElement pe1, SourceElement pe2) {
        if ( declarations0 == null ) {
            declarations0 = new LinkedList<SourceElement> ();
            declarations1 = new LinkedList<SourceElement> ();
        }

        declarations0.add ( 0, pe1 );
        declarations1.add ( 0, pe2 );
    }

    /** 
     * tests if the given elements have been assigned to the same
     * abstract name. 
     * @param pe0 SourceElement 
     * @param pe1 SourceElement 
     * @returns true if the pe1 and pe2 have been assigned to the same
     * name
     */
    public boolean sameAbstractName(SourceElement pe0, SourceElement pe1) {
        if ( declarations0 != null ) {
            final Iterator<SourceElement> it0 = declarations0.iterator ();
            final Iterator<SourceElement> it1 = declarations1.iterator ();

            while ( it0.hasNext () ) {
                // both lists are assumed to hold the same number of elements
                final Object o0 = it0.next ();
                final Object o1 = it1.next ();

                if ( pe0.equals ( o0 ) ) {
                    return pe1.equals ( o1 );
                } else if ( pe1.equals ( o1 ) ) {
                    return false;
                }
            }
        }
        
        return pe0.equals ( pe1 );
    }

}
