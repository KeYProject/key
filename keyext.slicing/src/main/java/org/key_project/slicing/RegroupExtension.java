/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing;

import java.util.ArrayList;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.control.InteractionListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
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

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

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
    private static final Logger LOGGER = LoggerFactory.getLogger(RegroupExtension.class);

    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        JToolBar bar = new JToolBar();
        JButton b = new JButton();
        b.setText("Reorder");
        b.addActionListener(e -> {
            KeYMediator m = MainWindow.getInstance().getMediator();
            Proof p = m.getSelectedProof();
            if (!p.closed()) {
                JOptionPane.showMessageDialog(MainWindow.getInstance(),
                    "Cannot reorder incomplete proof", "Error", JOptionPane.ERROR_MESSAGE);
                return;
            }
            try {
                var depTracker = m.getSelectedProof().lookup(DependencyTracker.class);
                if (depTracker == null) {
                    JOptionPane.showMessageDialog(MainWindow.getInstance(),
                        "Cannot reorder proof without dependency tracker", "Error",
                        JOptionPane.ERROR_MESSAGE);
                    return;
                }
                var depGraph = depTracker.getDependencyGraph();
                ProofReorder.reorderProof(m.getSelectedProof(), depGraph);
            } catch (Exception exc) {
                LOGGER.error("failed to reorder proof ", exc);
                MainWindow.getInstance().getMediator().startInterface(true);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), exc);
            }
        });
        bar.add(b);
        JButton b2 = new JButton();
        b2.setText("Regroup");
        b2.addActionListener(e -> {
            KeYMediator m = MainWindow.getInstance().getMediator();
            try {
                var depTracker = m.getSelectedProof().lookup(DependencyTracker.class);
                if (depTracker == null) {
                    JOptionPane.showMessageDialog(MainWindow.getInstance(),
                        "Cannot regroup proof without dependency tracker", "Error",
                        JOptionPane.ERROR_MESSAGE);
                    return;
                }
                var depGraph = depTracker.getDependencyGraph();
                ProofRegroup.regroupProof(m.getSelectedProof(), depGraph);
            } catch (Exception exc) {
                LOGGER.error("", exc);
                IssueDialog.showExceptionDialog(MainWindow.getInstance(), exc);
            }
        });
        bar.add(b2);
        return bar;
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
