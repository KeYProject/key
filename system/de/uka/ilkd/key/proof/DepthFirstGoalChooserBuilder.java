// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof;

public class DepthFirstGoalChooserBuilder implements GoalChooserBuilder {
 
	public static final String NAME = "Depth First Goal Chooser";
	
	public DepthFirstGoalChooserBuilder(){};
	
	public IGoalChooser create() {      
        return new DepthFirstGoalChooser();
    }
    
    public GoalChooserBuilder copy() {        
        return new DepthFirstGoalChooserBuilder();
    }   
    
    public String name() {
        return NAME;
    }
}
