/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.delayedcut;

import org.jspecify.annotations.NullMarked;

/**
 * Interface for DelayedCut listeners.
 *
 * @see DelayedCut
 * @see DelayedCutProcessor
 * @author Benjamin Niedermann
 */
@NullMarked
public interface DelayedCutListener {
    void eventCutting();

    void eventRebuildingTree(int currentTacletNumber, int totalNumber);

    void eventEnd(DelayedCut cutInformation);

    void eventException(Throwable throwable);
}
