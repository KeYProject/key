package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.PosInOccurrence;

/** Information about one modification of one node */
public interface NodeChange {

    /**
     * provides position information about the change
     *
     * @return position of change
     */
    PosInOccurrence getPos();

}
