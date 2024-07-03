/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.proof.ProofEvent;

/**
 * KeYListener is used for global changes that might affect most of
 * all KeY-Components.
 */
public interface KeYListener {

    /** invoked if a new proof has been loaded */
    void proofLoaded(ProofEvent e);

}
