// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io;

import java.util.List;

import de.uka.ilkd.key.parser.KeYParser;

/**
 * Defines the required which a {@link KeYParser} needs to parse a *.proof file
 * and to apply the rules again.
 * 
 * @author Martin Hentschel
 */
public interface IProofFileParser {

    /**
     * Enumeration of the different syntactic elements occurring in a saved
     * proof tree representation.
     * 
     * TODO: ProofSaver should not hardcode ids Enum names should be used
     * instead of rawnames (old proofs should be converted)
     * 
     * @author Richard Bubel
     */
    static enum ProofElementID {
        BRANCH("branch"), RULE("rule"), TERM("term"), FORMULA("formula"), INSTANTIATION(
                "inst"), ASSUMES_FORMULA_IN_SEQUENT("ifseqformula"), ASSUMES_FORMULA_DIRECT(
                "ifdirectformula"), RULESET("heur"), BUILT_IN_RULE("builtin"), CONTRACT(
                "contract"), ASSUMES_INST_BUILT_IN("ifInst"), JOIN_PROCEDURE(
                "joinProc"), NUMBER_JOIN_PARTNERS("nrJoinPartners"), JOIN_NODE(
                "joinNode"), JOIN_ID("joinId"), USER_INTERACTION(
                "userinteraction"), NEW_NAMES("newnames"), AUTOMODE_TIME(
                "autoModeTime"), KeY_LOG("keyLog"), KeY_USER("keyUser"), KeY_VERSION(
                "keyVersion"), KeY_SETTINGS("keySettings"), OPEN_GOAL(
                "opengoal");

        private String rawName;

        private ProofElementID(String rawName) {
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