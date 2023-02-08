/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.control;

import de.uka.ilkd.key.proof.ProofEvent;


public interface AutoModeListener {

    /**
     * invoked if automatic execution has started
     */
    void autoModeStarted(ProofEvent e);

    /**
     * invoked if automatic execution has stopped
     */
    void autoModeStopped(ProofEvent e);

}
