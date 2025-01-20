/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io.event;

import java.util.EventListener;

import de.uka.ilkd.key.proof.io.ProofSaver;

/**
 * Listens for changes on {@link ProofSaver} instances.
 *
 * @author Martin Hentschel
 */
public interface ProofSaverListener extends EventListener {
    /**
     * This method is called when a file was saved via {@link ProofSaver#save()}.
     *
     * @param e The {@link ProofSaverEvent}.
     */
    void proofSaved(ProofSaverEvent e);
}
