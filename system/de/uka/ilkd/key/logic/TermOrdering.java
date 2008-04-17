// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;


/**
 * Interface for term ordering
 */
public interface TermOrdering {

    /**
     * Compare the two given terms
     * @return a number negative, zero or a number positive if
     * <code>p_a</code> is less than, equal, or greater than
     * <code>p_b</code> regarding the ordering given by the
     * implementing class
     */
    int compare ( Term p_a, Term p_b );

}
