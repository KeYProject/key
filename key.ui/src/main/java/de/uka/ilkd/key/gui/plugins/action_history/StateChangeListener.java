/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.action_history;

import java.util.List;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.useractions.ProofRuleUserAction;
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
 * Listener object to record various user actions (currently only rule applications)
 * in the undo buffer.
 *
 * @author Arne Keller
 */
public class StateChangeListener implements InteractionListener {
    /**
     * The KeY mediator.
     */
    private final KeYMediator mediator;

    /**
     * Construct and register a new state change listener.
     *
     * @param mediator mediator
     */
    StateChangeListener(KeYMediator mediator) {
        this.mediator = mediator;
        mediator.getUI().getProofControl().addInteractionListener(this);
    }

    @Override
    public void settingChanged(Proof proof, Settings settings, SettingType type, String message) {

    }

    @Override
    public void runPrune(Node node) {

    }

    @Override
    public void runMacro(Node node, ProofMacro macro, PosInOccurrence posInOcc,
            ProofMacroFinishedInfo info) {

    }

    @Override
    public void runBuiltInRule(Node node, IBuiltInRuleApp app, BuiltInRule rule,
            PosInOccurrence pos, boolean forced) {

    }

    @Override
    public void runAutoMode(List<Node> initialGoals, Proof proof, ApplyStrategyInfo info) {

    }

    @Override
    public void runRule(Node goal, RuleApp app) {
        new ProofRuleUserAction(mediator, goal.proof(),
            goal, app.rule().displayName()).actionPerformed(null);
    }
}
