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