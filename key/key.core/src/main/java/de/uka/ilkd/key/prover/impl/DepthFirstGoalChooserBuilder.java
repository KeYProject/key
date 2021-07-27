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

package de.uka.ilkd.key.prover.impl;

import de.uka.ilkd.key.prover.GoalChooserBuilder;
import de.uka.ilkd.key.prover.GoalChooser;

public class DepthFirstGoalChooserBuilder implements GoalChooserBuilder {
 
	public static final String NAME = "Depth First Goal Chooser";
	
	public DepthFirstGoalChooserBuilder(){}

    public GoalChooser create() {
        return new DepthFirstGoalChooser();
    }
    
    public GoalChooserBuilder copy() {        
        return new DepthFirstGoalChooserBuilder();
    }   
    
    public String name() {
        return NAME;
    }
}