// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

/**
 *
 */
public interface RuleAppCost extends Comparable<RuleAppCost> {

    public int compareTo (RuleAppCost o);

    /**
     * Add the given costs to the costs that are represented by this object
     */
    RuleAppCost add (RuleAppCost cost2);

}
