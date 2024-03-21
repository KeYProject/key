/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;

/**
 * Data object about a proof branch cached on disk.
 *
 * @author Arne Keller
 */
public class CachedProofBranch {

    /**
     * File the cached proof is stored in.
     */
    public final Path proofFile;
    /**
     * Name of the cached proof.
     */
    public final String proofName;
    /**
     * The choice settings used in the proof.
     */
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
     * Referenced files the proof depends on.
     */
    private final Collection<CachedFile> referencedFiles;
    /**
     * Antecedent part of the sequent of the cached branch.
     */
    private final List<String> sequentAnte;
    /**
     * Succedent part of the sequent of the cached branch.
     */
    private final List<String> sequentSucc;
    /**
     * Types of the functions present on the sequent.
     */
    private final Map<String, String> typesFunctions;
    /**
     * Types of the location variables present on the sequent.
     */
    private final Map<String, String> typesLocVars;

    /**
     * Create a new data object about a cached proof branch.
     *
     * @param proofFile the file the proof is stored in
     * @param proofName the name of the cached proof
     * @param referencedFiles java/key files referenced by the proof
     * @param keyVersion KeY version used to save the proof
     * @param choiceSettings choice settings of the proof
     * @param stepIndex step index of the referenced node
     * @param sequent sequent of that node
     * @param services services of that node's proof
     */
    public CachedProofBranch(Path proofFile, String proofName,
            Collection<CachedFile> referencedFiles,
            String choiceSettings,
            String keyVersion,
            int stepIndex, Sequent sequent, Services services) {
        this.proofFile = proofFile;
        this.proofName = proofName;
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
     * @param proofName name of the cached proof
     * @param referencedFiles files referenced by the proof
     * @param choiceSettings choice settings of the proof
     * @param keyVersion KeY version used to save the cached proof branch
     * @param stepIndex step index of the referenced node
     * @param sequentAnte antecedent part of the sequent of that node
     * @param sequentSucc succedent part of the sequent of that node
     * @param typesFunctions types of the functions present in the sequent
     * @param typesLocVars types of the location variables present in the sequent
     */
    public CachedProofBranch(Path proofFile, String proofName,
            Collection<CachedFile> referencedFiles,
            String choiceSettings,
            String keyVersion,
            int stepIndex, List<String> sequentAnte, List<String> sequentSucc,
            Map<String, String> typesFunctions,
            Map<String, String> typesLocVars) {
        this.proofFile = proofFile;
        this.proofName = proofName;
        this.referencedFiles = referencedFiles;
        this.keyVersion = keyVersion;
        this.choiceSettings = choiceSettings;
        this.stepIndex = stepIndex;
        this.sequentAnte = sequentAnte;
        this.sequentSucc = sequentSucc;
        this.typesFunctions = typesFunctions;
        this.typesLocVars = typesLocVars;
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
    public boolean isCacheHitFor(Set<String> anteFormulas, Set<String> succFormulas,
            Sequent sequent) {
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

    public Collection<CachedFile> getReferencedFiles() {
        return Collections.unmodifiableCollection(referencedFiles);
    }

    public List<String> getSequentAnte() {
        return Collections.unmodifiableList(sequentAnte);
    }

    public List<String> getSequentSucc() {
        return Collections.unmodifiableList(sequentSucc);
    }
}
