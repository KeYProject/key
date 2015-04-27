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

package de.uka.ilkd.key.proof;

/**
 * creates the default goal chooser used in KeY
 */
public class DefaultGoalChooserBuilder implements GoalChooserBuilder {
    
    public static final String NAME = "Simple Goal Chooser";
    
    public DefaultGoalChooserBuilder() {}
    
    public IGoalChooser create() {      
        return new DefaultGoalChooser();
    }
    
    public String name() {
        return NAME;
    }

    public GoalChooserBuilder copy() {        
        return new DefaultGoalChooserBuilder();
    }    

}