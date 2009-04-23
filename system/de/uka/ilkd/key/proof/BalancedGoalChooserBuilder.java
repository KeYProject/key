// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof;

/**
 * builds a goal chooser taking care that loops are equally often 
 * unwound across different branches 
 *
 */
public class BalancedGoalChooserBuilder implements GoalChooserBuilder {

    public static final String NAME = "Balanced Goal Chooser";

    
    public BalancedGoalChooserBuilder() {}
    
    public IGoalChooser create() {        
        return new BalancedLoopGC();
    }

    public GoalChooserBuilder copy() {
        return new BalancedGoalChooserBuilder();
    }

    public String name() {
        return NAME;
    }

}
