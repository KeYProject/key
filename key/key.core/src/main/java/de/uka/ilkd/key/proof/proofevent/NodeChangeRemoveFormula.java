package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.PosInOccurrence;


/**
 * Information about a formula that has been removed from a node (the position given is the position
 * of the formula within the new sequent)
 */
public class NodeChangeRemoveFormula extends NodeChangeARFormula {
    public NodeChangeRemoveFormula(PosInOccurrence p_pos) {
        super(p_pos);
    }

    public String toString() {
        return "Formula removed: " + getPos();
    }
}
