// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;


/** 
 * This interface represents the variables that can be recognized 
 * by one of the parsers. 
 */
public interface ParsableVariable extends SortedOperator {
    /**
     * Returns an equivalent variable with the new name.
     * @param name  the new name
     * @return      equivalent operator with the new name
     */
    public Operator rename(Name name);
}
