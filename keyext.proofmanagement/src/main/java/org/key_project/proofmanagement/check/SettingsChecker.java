/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.util.*;

import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.speclang.Contract;

import org.key_project.proofmanagement.check.dependency.DependencyGraph;
import org.key_project.proofmanagement.check.dependency.DependencyNode;
import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.ProofBundleHandler;

import org.jspecify.annotations.NonNull;

// TODO: precise user feedback
// TODO: SMT settings ignored for now! (strategy settings should be irrelevant)

/**
 * This class checks if the settings of the given proofs are consistent. To do so, it is checked
 * that whenever a contract C is used in a proof where taclet options O are used, the taclet
 * settings for the proof of C are compatible (i.e., all the choices are in the compatibility
 * relation defined in this checker). For example, it is allowed to use a contract proven with
 * integer settings "intRules:arithmeticSemanticsCheckingOF" in a proof where
 * "intRules:arithmeticSemanticsIgnoringOF" is used, but not the other way round.
 * <p>
 * Note: This check will need to build the dependency graph between proofs and contracts.
 *
 * @author Jonas Krämer
 * @author Wolfram Pfeifer
 */
public class SettingsChecker implements Checker {
    /*
     * notes:
     * - every unique set of settings gets an id
     * - id is stored inside proof entry
     * - mapping from id to set of settings is shown in a table below the proof lines
     * - settings are checked for compatibility with dependency graph (compatibility relation)
     * - settings inconsistent to the first one are marked red in proof line, others green
     */

    // TODO: refactor the actual choices to not contain the name again (break loading of old proofs)
    // TODO: implement a possibility to define the relation in the key files (near the options)
    /*
     * The inner map defines the compatibility relation for taclet options (stored in a map again
     * for easy lookup). Having an entry (k,v) means that it is sound to use a contract proven with
     * option v in the proof of a contract where option k is active. Reflexive edges are implicit
     * and not stored in the map. Everything else is considered unsound. Note that for
     * "non-standard" options (that are not defined in optionsDecl.key in the taclet base) the
     * relation needs to be updated.
     */
    /*
     * TODO: With the (inner) map it is restricted to a (partial) function. We might need to
     * generalize to an arbitrary relation in the future ...
     */
    private static final Map<String, Map<String, String>> CHOICE_COMPAT_RELATION = new HashMap<>();
    static {
        CHOICE_COMPAT_RELATION.put("assertions", Map.of("assertions:on", "assertions:safe",
            "assertions:off", "asertions:safe"));
        CHOICE_COMPAT_RELATION.put("initialisation",
            Map.of("initialisation:disableStaticInitialisation",
                "initialisation:enableStaticInitialisation"));
        CHOICE_COMPAT_RELATION.put("intRules", Map.of("intRules:arithmeticSemanticsIgnoringOF",
            "intRules:arithmeticSemanticsCheckingOF",
            "intRules:javaSemantics",
            "intRules:arithmeticSemanticsIgnoringOF"));
        CHOICE_COMPAT_RELATION.put("programRules", Map.of("programRules:on", "programRules:off"));
        CHOICE_COMPAT_RELATION.put("runtimeExceptions", Map.of("runtimeExceptions:allow",
            "runtimeExceptions:ban",
            "runtimeExceptions:ignore",
            "runtimeExceptions:ban"));
        // choiceCompatibilityClasses.put("JavaCard", Map.of());
        CHOICE_COMPAT_RELATION.put("Strings", Map.of("Strings:on", "Strings:off"));
        CHOICE_COMPAT_RELATION.put("modelFields", Map.of("modelFields:treatAsAxiom",
            "modelFields:showSatisfiability"));
        CHOICE_COMPAT_RELATION.put("bigint", Map.of("bigint:on", "bigint:off"));
        CHOICE_COMPAT_RELATION.put("sequences", Map.of("sequences:on", "sequences:off"));
        CHOICE_COMPAT_RELATION.put("moreSeqRules", Map.of("moreSeqRules:off", "moreSeqRules:on"));
        CHOICE_COMPAT_RELATION.put("reach", Map.of("reach:on", "reach:off"));
        CHOICE_COMPAT_RELATION.put("integerSimplificationRules",
            Map.of("integerSimplificationRules:full", "integerSimplificationRules:minimal"));
        // choiceCompatibilityClasses.put("permissions", Map.of());
        // choiceCompatibilityClasses.put("wdOperator", Map.of());
        CHOICE_COMPAT_RELATION.put("wdChecks", Map.of("wdChecks:on", "wdChecks:off"));
        CHOICE_COMPAT_RELATION.put("mergeGenerateIsWeakeningGoal",
            Map.of("mergeGenerateIsWeakeningGoal:off", "mergeGenerateIsWeakeningGoal:on"));
        CHOICE_COMPAT_RELATION.put("methodExpansion",
            Map.of("methodExpansion:noRestriction", "methodExpansion:modularOnly"));
        CHOICE_COMPAT_RELATION.put("javaLoopTreatment", Map.of("javaLoopTreatment:efficient",
            "javaLoopTreatment:teaching",
            "javaLoopTreatment:teaching",
            "javaLoopTreatment:efficient"));
        CHOICE_COMPAT_RELATION.put("floatRules",
            Map.of("floatRules:assumeStrictfp", "floatRules:strictfpOnly"));
    }

    @Override
    public void check(ProofBundleHandler pbh, CheckerData data) throws ProofManagementException {
        data.addCheck("settings");
        data.print("Running settings checker ...");

        // load the proof ASTs
        KeYFacade.ensureProofsLoaded(data);

        /*
         * We need to build the dependency graph since we need to know which settings are used in
         * proofs of contracts of called methods.
         */
        KeYFacade.ensureDependencyGraphBuilt(data);

        boolean consistent = checkSettingsCompatibility(data);

        if (consistent) {
            data.setSettingsState(CheckerData.SettingsState.CONSISTENT);
            data.print(LogLevel.INFO, "All settings are consistent!");
        } else {
            data.setSettingsState(CheckerData.SettingsState.INCONSISTENT);
            data.print(LogLevel.WARNING, "Incompatible settings found!");
        }
        data.print(LogLevel.INFO, "Settings check completed!");
    }

    private boolean checkSettingsCompatibility(CheckerData data) {
        boolean consistent = true;
        DependencyGraph graph = data.getDependencyGraph();
        List<ChoiceSettings> choiceSettings = new ArrayList<>();

        // check that all edges are in the compatibility relation
        for (DependencyNode node : graph.getNodes()) {

            Contract srcContr = node.getContract();
            CheckerData.ProofEntry proofEntry = data.getProofEntryByContract(srcContr);

            if (proofEntry == null) {
                /*
                 * This is the case for contracts that have no proof in the bundle, in particular
                 * for contracts from JavaRedux. These nodes should not be the starting point of any
                 * edges.
                 */
                if (!node.getDependencies().isEmpty()) {
                    throw new IllegalStateException(srcContr.getName() + " should not have "
                        + "outgoing edges in the dependency graph!");
                }
                continue;
            }
            ChoiceSettings srcSettings = proofEntry.proof.getSettings().getChoiceSettings();
            choiceSettings.add(srcSettings);

            for (DependencyNode edge : node.getDependencies().keySet()) {

                Contract targetContr = edge.getContract();
                CheckerData.ProofEntry targetProofEntry = data.getProofEntryByContract(targetContr);
                if (targetProofEntry == null) {
                    // this is the case for contracts that have not proof in the bundle, in
                    // particular for contracts from JavaRedux
                    // TODO: for now, we ignore these edges
                    continue;
                }
                ChoiceSettings targetSettings =
                    targetProofEntry.proof.getSettings().getChoiceSettings();
                choiceSettings.add(targetSettings);

                if (!choicesCompatible(srcSettings, targetSettings, data)) {
                    consistent = false;
                }
            }
        }

        // TODO: this does some work a second time (like iterating through all the choices) ...
        // creates the mapping of choicesSettings to the proofs and assigns reference ids
        generateSettingsIds(choiceSettings, data);

        return consistent;
    }

    /*
     * Checks if the given choice settings are compatible, i.e. all the choices are in the relation
     * defined above.
     */
    private boolean choicesCompatible(@NonNull ChoiceSettings srcSettings,
            @NonNull ChoiceSettings targetSettings,
            @NonNull CheckerData data) {
        boolean compatible = true;

        for (String category : srcSettings.getDefaultChoices().keySet()) {
            String srcChoice = srcSettings.getDefaultChoices().get(category);
            String targetChoice = targetSettings.getDefaultChoices().get(category);
            if (!choicesCompatible(category, srcChoice, targetChoice)) {
                // do not return immediately; we want to give feedback about all settings
                // return false;
                compatible = false;
                data.print(LogLevel.WARNING, "In proof under option " + srcChoice + ", it is "
                    + "unsound to use a contract proven under " + targetChoice);
            }
        }
        return compatible;
    }

    /*
     * Checks whether two given choices are compatible. They are considered compatible if they are
     * in the relation given by the map above or if they are equal (the relation is implicitly
     * reflexive).
     */
    private boolean choicesCompatible(@NonNull String name, @NonNull String srcChoice,
            @NonNull String targetChoice) {
        if (srcChoice.equals(targetChoice)) {
            // the relation is (implicitly) reflexive!
            return true;
        }
        Map<String, String> rel = CHOICE_COMPAT_RELATION.get(name);
        if (rel == null || rel.isEmpty()) {
            // unknown or no compatibility for this category: only sound if both values are equal
            return false;
        }
        // sufficient for a partial function, but might need to generalize to arbitrary relation ...
        return rel.getOrDefault(srcChoice, "").equals(targetChoice);
    }

    // TODO change to map Settings -> ProofEntry (for better feedback)?
    private static void generateSettingsIds(@NonNull List<@NonNull ChoiceSettings> choiceSettings,
            @NonNull CheckerData data) {
        if (choiceSettings.isEmpty()) {
            return;
        }

        // store reference settings in data with id 0
        ChoiceSettings reference = choiceSettings.getFirst();
        Map<String, String> refChoices = reference.getDefaultChoices();
        data.addReferenceChoices(refChoices);
        data.print(LogLevel.DEBUG, "Reference settings (id 0) are: " + refChoices);

        for (int i = 1; i < choiceSettings.size(); i++) {
            Map<String, String> cs = choiceSettings.get(i).getDefaultChoices();

            // settings are only added (with fresh id) if they are unique currently
            if (!data.getChoices2Id().containsKey(cs)) {
                // add to settings map with next free id
                data.addReferenceChoices(cs);

                data.print(LogLevel.DEBUG, "Found (currently) unique settings (assigned id " +
                    data.getChoices2Id().get(cs) + "): " + cs);

                // at least one of the entries is different:
                // in this case we have to check if all entries are compatible
                // (w.r.t. the compatibility classes defined above)
                if (!cs.keySet().equals(refChoices.keySet())) {
                    // one of them has a setting with an additional key
                    data.print(LogLevel.DEBUG, "Incompatible (additional key found)!");
                }
            } else {
                // add a map entry for lookup
                data.addChoices(cs);
                // settings from cs are identical to reference
                data.print(LogLevel.DEBUG, "Settings already in use with id " +
                    data.getChoices2Id().get(cs) + ": " + cs);
            }
        }
    }
}
