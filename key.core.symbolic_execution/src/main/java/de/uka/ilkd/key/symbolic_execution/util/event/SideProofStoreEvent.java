/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.util.event;

import java.util.EventObject;

import de.uka.ilkd.key.symbolic_execution.util.SideProofStore;
import de.uka.ilkd.key.symbolic_execution.util.SideProofStore.Entry;

/**
 * An event thrown by a {@link SideProofStore} and observed via an {@link ISideProofStoreListener}.
 *
 * @author Martin Hentschel
 */
public class SideProofStoreEvent extends EventObject {
    /**
     * Generated UID.
     */
    private static final long serialVersionUID = 8046460017292232070L;

    /**
     * The added or removed {@link Entry}s.
     */
    private final Entry[] entries;

    /**
     * Constructor.
     *
     * @param source The source.
     * @param entries The added or removed {@link Entry}s.
     */
    public SideProofStoreEvent(SideProofStore source, Entry[] entries) {
        super(source);
        this.entries = entries;
    }

    /**
     * Returns the added or removed {@link Entry}s.
     *
     * @return The added or removed {@link Entry}s.
     */
    public Entry[] getEntries() {
        return entries;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public SideProofStore getSource() {
        return (SideProofStore) super.getSource();
    }
}
