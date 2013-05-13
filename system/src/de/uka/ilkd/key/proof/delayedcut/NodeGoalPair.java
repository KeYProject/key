// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.delayedcut;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

public class NodeGoalPair{
    public final Node node; 
    public final Goal goal;
    public NodeGoalPair(Node node, Goal goal) {
        super();
        this.node = node;
        this.goal = goal;
    }
    
}