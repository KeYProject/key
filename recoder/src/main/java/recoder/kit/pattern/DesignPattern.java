/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
