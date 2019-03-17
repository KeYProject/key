package de.uka.ilkd.key.control;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.Settings;

import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (08.12.18)
 */
public interface InteractionListener {
    void settingChanged(Proof proof, Settings settings, SettingType type, String message);

    void runPrune(Node node);

    void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc, ProofMacroFinishedInfo info);

    void runBuiltInRule(Goal goal, IBuiltInRuleApp app, BuiltInRule rule,
                        PosInOccurrence pos, boolean forced);

    void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info);

    void runRule(Goal goal, RuleApp app);


    public enum SettingType {
        SMT, CHOICE, STRATEGY
    }
}
