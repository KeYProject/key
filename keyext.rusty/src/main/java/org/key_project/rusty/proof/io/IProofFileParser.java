/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.util.List;

public interface IProofFileParser {
    enum ProofElementID {
        BRANCH("branch"), RULE("rule"), TERM("term"), FORMULA("formula"), INSTANTIATION("inst"),
        ASSUMES_FORMULA_IN_SEQUENT("assumesSeqFormula"), ASSUMES_FORMULA_DIRECT("ifdirectformula"),
        RULESET("heur"), BUILT_IN_RULE("builtin"), CONTRACT("contract"),
        ASSUMES_INST_BUILT_IN("ifInst"), MERGE_ABSTRACTION_PREDICATES("abstractionPredicates"),
        MERGE_PREDICATE_ABSTRACTION_LATTICE_TYPE("latticeType"), MERGE_PROCEDURE("mergeProc"),
        NUMBER_MERGE_PARTNERS("nrMergePartners"), MERGE_NODE("mergeNode"), MERGE_ID("mergeId"),
        MERGE_DIST_FORMULA("distFormula"), MERGE_USER_CHOICES("userChoices"),
        USER_INTERACTION("userinteraction"), PROOF_SCRIPT("proofscript"), NEW_NAMES("newnames"),
        AUTOMODE_TIME("autoModeTime"), KeY_LOG("keyLog"), KeY_USER("keyUser"),
        KeY_VERSION("keyVersion"), KeY_SETTINGS("keySettings"), OPEN_GOAL("opengoal"),
        NOTES("notes"), SOLVERTYPE("solverType"), MODALITY("modality");

        private final String rawName;

        ProofElementID(String rawName) {
            this.rawName = rawName;
        }

        public String getRawName() {
            return rawName;
        }

    }

    void beginExpr(ProofElementID eid, String str);

    void endExpr(ProofElementID eid, int stringLiteralLine);

    String getStatus();

    List<Throwable> getErrors();
}
