// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;


/**
 * Interface for a class (function, predicate) from which instances
 * exist for every sort (e.g. the functions/predicates of the
 * collection sorts)
 */
public interface SortDependingSymbol extends Named {
    
    /**
     * @return the sort this object has been instantiated for
     */
    Sort                getSortDependingOn ();

    /**
     * Compares "this" and "p"
     * @param p object to compare
     * @return true iff this and p are instances of the same kind of
     * symbol, but possibly instantiated for different sorts
     */
    boolean             isSimilar      ( SortDependingSymbol p );

    /**
     * Assign a name to this term symbol, independant of concrete
     * instantiations for different sorts
     * @return the kind of term symbol this object is an instantiation
     * for
     */
    Name                getKind        ();

    /**
     * Get the instance of this term symbol defined by the given sort
     * "p_sort"
     * @return a term symbol similar to this one, or null if this
     * symbol is not defined by "p_sort"
     *
     * POSTCONDITION: result==null || (this.isSimilar(result) &&
     * result.getSortDependingOn()==p_sort)
     */
    SortDependingSymbol getInstanceFor ( SortDefiningSymbols p_sort );

}
