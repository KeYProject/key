/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.io.File;

/**
 * Data object about a cached proof branch.
 *
 * @see CachingDatabase
 * @author Arne Keller
 */
public class CachedProofBranch {
    /**
     * File the cached proof is stored in.
     */
    public final File proofFile;
    public final String choiceSettings;
    /**
     * Step index of the cached branch.
     */
    public final int stepIndex;

    /**
     * Sequent of the cached branch.
     */
    public final String sequent;

    /**
     * Create a new data object about a cached proof branch.
     *
     * @param proofFile the file the proof is stored in
     * @param choiceSettings choice settings of the proof
     * @param stepIndex step index of the referenced node
     * @param sequent sequent of that node
     */
    CachedProofBranch(File proofFile, String choiceSettings, int stepIndex, String sequent) {
        this.proofFile = proofFile;
        this.choiceSettings = choiceSettings;
        this.stepIndex = stepIndex;
        this.sequent = sequent;
    }
}
