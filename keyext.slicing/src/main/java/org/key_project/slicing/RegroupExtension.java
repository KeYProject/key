/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.gui.settings.SettingsProvider;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Proof regrouping and reordering extension.
 *
 * @author Arne Keller
 */
@KeYGuiExtension.Info(name = "Reordering and regrouping",
    description = "Author: Arne Keller <arne.keller@posteo.de>",
    experimental = false,
    optional = true,
    priority = 9001)
public class RegroupExtension implements KeYGuiExtension,
        KeYGuiExtension.Startup, KeYGuiExtension.Settings,
        KeYGuiExtension.Toolbar, InteractionListener {

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        return new JToolBar();
    }

    @Override
    public SettingsProvider getSettings() {
        return new ProofRegroupSettingsProvider();
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        mediator.getUI().getProofControl().addInteractionListener(this);
    }

    @Override
    public void runPrune(Node node) {
        if (node.isHideInProofTree()) {
            // Perhaps there are some nodes below the prune target in this group.
            // These should be removed from the proof tree view.
            var groupNode = node.parent();
            while (groupNode.getGroup() == null) {
                var prev = groupNode;
                groupNode = groupNode.parent();
                // robustness: no infinite loop
                // (should never happen anyhow)
                if (prev == groupNode) {
                    return;
                }
            }
            var groupNodes = groupNode.getGroup();
            var removedAfter = groupNodes.indexOf(node);
            groupNode.setGroup(new ArrayList<>(groupNodes.subList(0, removedAfter + 1)));
        }
    }

    @Override
    public void settingChanged(Proof proof, de.uka.ilkd.key.settings.Settings settings,
            SettingType type, String message) {

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

    }
}
