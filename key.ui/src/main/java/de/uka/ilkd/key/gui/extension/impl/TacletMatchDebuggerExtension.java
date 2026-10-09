/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.extension.impl;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.extension.api.ContextMenuAdapter;
import de.uka.ilkd.key.gui.extension.api.ContextMenuKind;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Term;
import org.key_project.prover.rules.TacletMatcher;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.instantiation.SVInstantiations;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Extension that provides a context menu action for debugging taclet matching on terms.
 * When clicking on a term in the sequent view, users can select a taclet from a combo box
 * and see whether it matches the selected term.
 *
 * @author Alexander Weigl
 */
@KeYGuiExtension.Info(name = "Taclet Match Debugger",
    description = "Debug taclet matching by selecting a term and testing which taclets match.\n"
        + "Developer: Alexander Weigl",
    experimental = false, optional = true, priority = 50)
@NullMarked
public class TacletMatchDebuggerExtension implements KeYGuiExtension, KeYGuiExtension.ContextMenu {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(TacletMatchDebuggerExtension.class);

    private final ContextMenuAdapter adapter = new ContextMenuAdapter() {
        @Override
        public <T> List<Action> getContextActions(KeYMediator mediator, ContextMenuKind<T> kind,
                @Nullable T underlyingObject) {
            if (kind != ContextMenuKind.SEQUENT_VIEW
                    || !(underlyingObject instanceof PosInSequent pos)) {
                return Collections.emptyList();
            }

            // Check if we have a valid proof and goal
            Goal goal = mediator.getSelectedGoal();
            if (goal == null) {
                return Collections.emptyList();
            }

            // Check if the position has a valid term
            if (pos.getPosInOccurrence() == null) {
                return Collections.emptyList();
            }

            var selectedTerm = pos.getPosInOccurrence().subTerm();
            if (selectedTerm == null) {
                return Collections.emptyList();
            }

            return Collections.singletonList(new MatchTacletAction(mediator, pos, selectedTerm));
        }
    };

    @Override
    public <T> List<Action> getContextActions(KeYMediator mediator, ContextMenuKind<T> kind,
            @Nullable T underlyingObject) {
        return adapter.getContextActions(mediator, kind, underlyingObject);
    }

    /**
     * Action that opens a dialog to select a taclet and test matching.
     */
    private static class MatchTacletAction extends KeyAction {
        private final KeYMediator mediator;
        private final PosInSequent pos;
        private final Term selectedTerm;

        public MatchTacletAction(KeYMediator mediator, PosInSequent pos, Term selectedTerm) {
            this.mediator = mediator;
            this.pos = pos;
            this.selectedTerm = selectedTerm;
            setName("Match Taclets...");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            MainWindow mainWindow = MainWindow.getInstance();

            // Get all available taclets from the current goal
            Goal goal = mediator.getSelectedGoal();
            if (goal == null) {
                JOptionPane.showMessageDialog(mainWindow,
                    "No active proof goal available.",
                    "Error",
                    JOptionPane.ERROR_MESSAGE);
                return;
            }

            // Collect all taclets
            List<NoPosTacletApp> tacletApps = new ArrayList<>(
                goal.ruleAppIndex().tacletIndex().allNoPosTacletApps());

            // Add taclets from OneStepSimplifier if available
            var simplifier = MiscTools.findOneStepSimplifier(goal.proof());
            if (simplifier != null && !simplifier.isShutdown()) {
                tacletApps.addAll(simplifier.getCapturedTaclets());
            }

            if (tacletApps.isEmpty()) {
                JOptionPane.showMessageDialog(mainWindow,
                    "No taclets available for matching.",
                    "Information",
                    JOptionPane.INFORMATION_MESSAGE);
                return;
            }

            // Sort taclets by name for easier selection
            tacletApps.sort(Comparator.comparing(app -> app.rule().name().toString()));

            // Create array of taclet names for the combo box
            String[] tacletNames = tacletApps.stream()
                    .map(app -> app.rule().name().toString())
                    .toArray(String[]::new);

            // Show dialog with combo box for taclet selection
            JComboBox<String> tacletComboBox = new JComboBox<>(tacletNames);
            tacletComboBox.setEditable(false);
            tacletComboBox.setMaximumRowCount(25);

            JPanel panel = new JPanel(new BorderLayout());
            panel.add(new JLabel("Select a taclet to match against the term:"), BorderLayout.NORTH);
            panel.add(tacletComboBox, BorderLayout.CENTER);
            panel.setBorder(BorderFactory.createEmptyBorder(10, 10, 10, 10));

            int result = JOptionPane.showConfirmDialog(
                mainWindow,
                panel,
                "Match Taclet",
                JOptionPane.OK_CANCEL_OPTION,
                JOptionPane.PLAIN_MESSAGE);

            if (result == JOptionPane.OK_OPTION) {
                int selectedIndex = tacletComboBox.getSelectedIndex();
                if (selectedIndex >= 0 && selectedIndex < tacletApps.size()) {
                    NoPosTacletApp selectedTacletApp = tacletApps.get(selectedIndex);
                    Taclet selectedTaclet = selectedTacletApp.rule();

                    performMatching(selectedTaclet, selectedTerm, goal);
                }
            }
        }

        /**
         * Performs the actual taclet matching and displays the results.
         */
        private void performMatching(Taclet taclet, Term term, Goal goal) {
            StringWriter out = new StringWriter();
            PrintWriter output = new PrintWriter(out);
            var services = goal.proof().getServices();
            TacletMatcher matcher = new VMTacletMatcher(taclet, output);

            output.printf("=== Taclet Match Debug ===\n\n");
            output.printf("Selected Term: %s\n\n", term);
            output.printf("Selected Taclet: %s\n\n", taclet.name());

            // Print taclet definition
            output.printf("Taclet Definition:\n");
            output.printf("----------------------------------------\n");
            try {
                var lp = de.uka.ilkd.key.pp.LogicPrinter.purePrinter(
                    new de.uka.ilkd.key.pp.NotationInfo(), null);
                lp.printTaclet(taclet);
                output.println(lp.result());
            } catch (Exception ex) {
                output.printf("Could not print taclet: %s\n", ex.getMessage());
            }
            output.printf("----------------------------------------\n\n");

            // Try to match
            output.printf("Matching Result:\n");
            output.printf("----------------------------------------\n");

            try {
                // Create initial match conditions
                MatchResultInfo initialMatchCond = MatchConditions.EMPTY_MATCHCONDITIONS;

                MatchResultInfo matchResult = matcher.matchFind(term, initialMatchCond, services);

                if (matchResult != null) {
                    output.printf("✓ MATCH SUCCESSFUL!\n\n");

                    // Print variable instantiations
                    SVInstantiations instantiations = matchResult.getInstantiations();
                    var instMap = instantiations.getInstantiationMap();
                    if (instMap != null && !instMap.isEmpty()) {
                        output.printf("Variable Instantiations:\n");
                        for (var entry : instMap) {
                            output.printf("  %s := %s\n", entry.key().name(),
                                entry.value().getInstantiation());
                        }
                    } else {
                        output.printf("No variable instantiations needed.\n");
                    }

                    // Check additional conditions
                    MatchResultInfo checkedResult = matcher.checkConditions(matchResult, services);
                    if (checkedResult != null) {
                        output.printf("\n✓ All taclet conditions satisfied!\n");
                    } else {
                        output.printf("\n✗ Taclet conditions NOT satisfied!\n");
                    }
                } else {
                    output.printf("✗ NO MATCH - The taclet does not match the selected term.\n");
                }
            } catch (Exception ex) {
                output.printf("✗ ERROR during matching: ").printf(ex.getMessage()).printf("\n");
                LOGGER.error("Error during taclet matching", ex);
            }

            output.printf("----------------------------------------\n");

            // Output to console
            LOGGER.info("Taclet matching performed for taclet: {}, {}", taclet.name(), out);

            // Also show in a dialog
            JTextArea textArea = new JTextArea(out.toString());
            textArea.setEditable(false);
            textArea.setCaretPosition(0);
            textArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));

            JScrollPane scrollPane = new JScrollPane(textArea);
            scrollPane.setPreferredSize(new Dimension(700, 500));

            JOptionPane.showMessageDialog(
                MainWindow.getInstance(),
                scrollPane,
                "Taclet Match Result",
                JOptionPane.INFORMATION_MESSAGE);
        }
    }
}
