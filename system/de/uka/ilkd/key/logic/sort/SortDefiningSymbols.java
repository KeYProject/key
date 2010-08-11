// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic.sort;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.SortDependingSymbol;


/**
 * Interface for sorts having specific symbols
 * (e.g. functions/predicates of collection sorts)
 */
public interface SortDefiningSymbols extends Sort {
    
    /**
     * Creates symbols defined by this sort and inserts them into the
     * namespace "functions".
     * @param functions Namespace to which functions and predicates
     * should be added to
     * @param sorts the Namespace containing all known sorts
     */
    void addDefinedSymbols(Namespace functions, Namespace sorts);
    
    /**
     * Lookup the symbol of kind "p_name", which is a sort
     * independent identifier for this symbol
     * @return Symbol with (kind) name "p_name"
     * ("ret.getKind().equals(p_name)"), null if no such object exists
     */
    SortDependingSymbol lookupSymbol  ( Name      p_name );

}
