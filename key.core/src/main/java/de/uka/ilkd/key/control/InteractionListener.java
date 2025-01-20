/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control;

import java.util.List;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.Settings;

/**
 * @author Alexander Weigl
 * @version 1 (08.12.18)
 */
public interface InteractionListener {
    void settingChanged(Proof proof, Settings settings, SettingType type, String message);

    void runPrune(Node node);

    void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc,
            ProofMacroFinishedInfo info);

    void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule, PosInOccurrence pos,
            boolean forced);

    void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info);

    void runRule(Node goal, RuleApp app);

    enum SettingType {
        SMT, CHOICE, STRATEGY
    }
}
