/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.util.event;

import java.util.EventListener;

import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;

/**
 * Observes changes on a {@link SideProofStore}.
 *
 * @author Martin Hentschel
 */
public interface ISideProofStoreListener extends EventListener {
    /**
     * When new {@link Entry}s are added.
     *
     * @param e The {@link SideProofStoreEvent}.
     */
    void entriesAdded(SideProofStoreEvent e);

    /**
     * When existing {@link Entry}s were removed.
     *
     * @param e The {@link SideProofStoreEvent}.
     */
    void entriesRemoved(SideProofStoreEvent e);
}
