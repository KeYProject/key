// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit.pattern;

import recoder.ModelElement;

/**
 * Design pattern.
 *
 * @author <TT>AutoDoc</TT>
 * @author AL
 */
public interface DesignPattern extends ModelElement {

    /**
     * Get total number of participants.
     *
     * @return the number of participants.
     */
    int getParticipantCount();

    /**
     * Get a participants by its index.
     *
     * @param index an index of a participant.
     * @return the participant.
     * @throws IndexOutOfBoundsException, if the index is not in bounds.
     */
    ModelElement getParticipantAt(int index);
}
