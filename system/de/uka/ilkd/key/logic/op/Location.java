// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.sort.Sort;

/** 
 * Operators implementing this interface may stand for
 * locations as well. This means e.g. occur as top level operators on the 
 * left side of an assignment pair of an update. 
 */
public interface Location extends Operator, NonRigid {
    /**
     * Checks if location <code>loc</code> may be an alias of the current
     * location.
     * The <code>mayBeAliasOf</code> relation is <strong>not</strong> necessary 
     * symmetric as e.g. for attributes and their shadowed variant. 
     * @param loc the Location to check 
     * @return true if <code>loc</loc> may be an alias of the current operator
     */
    boolean mayBeAliasedBy(Location loc);
    
    /**
     * returns the sort of the location
     */
    Sort sort();
}
