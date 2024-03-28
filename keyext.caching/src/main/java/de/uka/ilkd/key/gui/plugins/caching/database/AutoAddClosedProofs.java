/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching.database;

import java.io.IOException;
import java.util.Collections;
import java.util.Set;
import java.util.WeakHashMap;

import de.uka.ilkd.key.gui.plugins.caching.settings.CachingSettingsProvider;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Proof tree listener that automatically adds proofs to the caching database.
 *
 * @author Arne Keller
 */
public class AutoAddClosedProofs implements ProofTreeListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(AutoAddClosedProofs.class);
    /**
     * The database to add proofs to.
     */
    private final CachingDatabase database;
    /**
     * Already added proofs.
     */
    private final Set<Proof> addedProofs = Collections.newSetFromMap(new WeakHashMap<>());

    /**
     * Create a new handler.
     *
     * @param database the database to add proofs to
     */
    public AutoAddClosedProofs(CachingDatabase database) {
        this.database = database;
    }

    @Override
    public void proofClosed(ProofTreeEvent e) {
        // first, check whether this functionality is enabled
        var settings = CachingSettingsProvider.getCachingSettings();
        if (!settings.getAutoAddClosedProofs()) {
            return;
        }

        Proof proof = e.getSource();
        // only add a proof to the database once
        if (addedProofs.contains(proof)) {
            return;
        }
        addedProofs.add(proof);
        try {
            database.addProof(proof);
        } catch (IOException ex) {
            LOGGER.error("failed to add proof to database ", ex);
        }
    }
}
