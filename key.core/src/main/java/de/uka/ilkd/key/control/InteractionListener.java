/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control;

import java.util.List;

import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.settings.Settings;

import org.key_project.prover.engine.ProofSearchInformation;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;

/**
 * @author Alexander Weigl
 * @version 1 (08.12.18)
 */
public interface InteractionListener {
    void settingChanged(Proof proof, Settings settings, SettingType type, String message);

    void runPrune(Node node);

    void runMacro(Node node, ProofMacro macro,
            PosInOccurrence posInOcc,
            ProofMacroFinishedInfo info);

    void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos,
            boolean forced);

    void runAutoMode(List<Node> initialGoals, Proof proof,
            ProofSearchInformation<Proof, Goal> info);

    void runRule(Node goal, RuleApp app);

    enum SettingType {
        SMT, CHOICE, STRATEGY
    }
}
