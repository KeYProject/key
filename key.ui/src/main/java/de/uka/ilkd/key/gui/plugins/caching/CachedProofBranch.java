/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;

import java.io.File;
import java.util.Collection;

/**
 * Data object about a cached proof branch.
 *
 * (see CachingDatabase)
 *
 * @author Arne Keller
 */
public class CachedProofBranch {
    /**
     * File the cached proof is stored in.
     */
    public final File proofFile;
    /**
     * Referenced files the proof depends on.
     */
    public final Collection<CachedFile> referencedFiles;
    public final String choiceSettings;
    /**
     * KeY version used to create the proof.
     */
    public final String keyVersion;
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
     * @param services services of that node's proof
     */
    CachedProofBranch(File proofFile, Collection<CachedFile> referencedFiles, String choiceSettings,
                      String keyVersion,
                      int stepIndex, Sequent sequent, Services services) {
        this.proofFile = proofFile;
        this.referencedFiles = referencedFiles;
        this.keyVersion = keyVersion;
        this.choiceSettings = choiceSettings;
        this.stepIndex = stepIndex;
        var sb = new StringBuilder();
        var ante = sequent.antecedent();
        for (int i = 0; i < ante.size(); i++) {
            sb.append(LogicPrinter.quickPrintTerm(ante.get(i).formula(), services));
            if (i < ante.size() - 1) {
                sb.append(",");
            }
        }
        sb.append("==>");
        var succ = sequent.succedent();
        for (int i = 0; i < succ.size(); i++) {
            sb.append(LogicPrinter.quickPrintTerm(succ.get(i).formula(), services));
            if (i < succ.size() - 1) {
                sb.append(",");
            }
        }
        this.sequent = sb.toString();
    }

    /**
     * Create a new data object about a cached proof branch.
     *
     * @param proofFile the file the proof is stored in
     * @param choiceSettings choice settings of the proof
     * @param stepIndex step index of the referenced node
     * @param sequent sequent of that node
     */
    CachedProofBranch(File proofFile, Collection<CachedFile> referencedFiles, String choiceSettings,
                      String keyVersion,
                      int stepIndex, String sequent) {
        this.proofFile = proofFile;
        this.referencedFiles = referencedFiles;
        this.keyVersion = keyVersion;
        this.choiceSettings = choiceSettings;
        this.stepIndex = stepIndex;
        this.sequent = sequent;
    }
}
