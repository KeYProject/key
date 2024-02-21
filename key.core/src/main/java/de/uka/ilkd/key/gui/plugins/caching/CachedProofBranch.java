/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.io.File;
import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;

/**
 * Data object about a cached proof branch.
 *
 * (see CachingDatabase)
 *
 * @author Arne Keller
 */
public class CachedProofBranch {
    private static final String SEQUENT_ANTE_SUCC_SEPARATOR = "====>";
    private static final String SEQUENT_TERM_SEPARATOR = ",,";

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
     * Antecedent part of the sequent of the cached branch.
     */
    public final List<String> sequentAnte;
    /**
     * Succedent part of the sequent of the cached branch.
     */
    public final List<String> sequentSucc;
    private final Map<String, String> typesFunctions;
    private final Map<String, String> typesLocVars;

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
        this.sequentAnte = new ArrayList<>();
        var ante = sequent.antecedent();
        for (int i = 0; i < ante.size(); i++) {
            sequentAnte.add(
                LogicPrinter.quickPrintTerm(ante.get(i).formula(), services, true, false, false));
        }
        this.sequentSucc = new ArrayList<>();
        var succ = sequent.succedent();
        for (int i = 0; i < succ.size(); i++) {
            sequentSucc.add(
                LogicPrinter.quickPrintTerm(succ.get(i).formula(), services, true, false, false));
        }
        var typeCollector = new TypeCollectingVisitor();
        typeCollector.visit(sequent);

        this.typesFunctions = typeCollector.getTypes();
        this.typesLocVars = typeCollector.getTypesLocVars();
    }

    /**
     * Create a new data object about a cached proof branch.
     *
     * @param proofFile the file the proof is stored in
     * @param choiceSettings choice settings of the proof
     * @param stepIndex step index of the referenced node
     * @param sequent sequent of that node (encoded by {@link #encodeSequent()})
     */
    CachedProofBranch(File proofFile, Collection<CachedFile> referencedFiles, String choiceSettings,
            String keyVersion,
            int stepIndex, String sequent, Map<String, String> typesFunctions, Map<String, String> typesLocVars) {
        this.proofFile = proofFile;
        this.referencedFiles = referencedFiles;
        this.keyVersion = keyVersion;
        this.choiceSettings = choiceSettings;
        this.stepIndex = stepIndex;
        var anteSucc = sequent.split(SEQUENT_ANTE_SUCC_SEPARATOR, 2);
        if (anteSucc.length != 2) {
            throw new IllegalArgumentException("expected sequent to contain separator");
        }
        var ante = anteSucc[0].split(SEQUENT_TERM_SEPARATOR);
        this.sequentAnte = Arrays.asList(ante);
        var succ = anteSucc[1].split(SEQUENT_TERM_SEPARATOR);
        this.sequentSucc = Arrays.asList(succ);
        this.typesFunctions = typesFunctions;
        this.typesLocVars = typesLocVars;
    }

    public String encodeSequent() {
        var sb = new StringBuilder();

        for (int i = 0; i < sequentAnte.size(); i++) {
            sb.append(sequentAnte.get(i));
            if (i != sequentAnte.size() - 1) {
                sb.append(SEQUENT_TERM_SEPARATOR);
            }
        }
        sb.append(SEQUENT_ANTE_SUCC_SEPARATOR);
        for (int i = 0; i < sequentSucc.size(); i++) {
            sb.append(sequentSucc.get(i));
            if (i != sequentSucc.size() - 1) {
                sb.append(SEQUENT_TERM_SEPARATOR);
            }
        }

        return sb.toString();
    }

    /**
     * Determine whether this cached proof branch can be used to close the provided sequent.
     * Returns true if the provided formulas are a superset of this branch.
     *
     * @param anteFormulas antecedent
     * @param succFormulas succedent
     * @param sequent the sequent
     * @return whether this cached proof branch can close the new proof branch
     */
    public boolean isCacheHitFor(Set<String> anteFormulas, Set<String> succFormulas, Sequent sequent) {
        var typeCollector = new TypeCollectingVisitor();
        typeCollector.visit(sequent);
        for (var entry : typeCollector.getTypes().entrySet()) {
            var ourType = typesFunctions.get(entry.getKey());
            if (ourType == null) {
                continue;
            }
            if (!ourType.equals(entry.getValue())) {
                return false;
            }
        }
        for (var entry : typeCollector.getTypesLocVars().entrySet()) {
            var ourType = typesLocVars.get(entry.getKey());
            if (ourType == null) {
                continue;
            }
            if (!ourType.equals(entry.getValue())) {
                return false;
            }
        }
        for (var ante : sequentAnte) {
            if (!anteFormulas.contains(ante)) {
                return false;
            }
        }
        for (var succ : sequentSucc) {
            if (!succFormulas.contains(succ)) {
                return false;
            }
        }
        return true;
    }

    public Map<String, String> getTypesFunctions() {
        return Collections.unmodifiableMap(typesFunctions);
    }

    public Map<String, String> getTypesLocVars() {
        return Collections.unmodifiableMap(typesLocVars);
    }
}
