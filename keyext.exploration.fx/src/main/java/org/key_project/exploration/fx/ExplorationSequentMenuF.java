/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.fx;

import java.util.List;
import java.util.Optional;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.control.Alert;
import javafx.scene.control.MenuItem;
import javafx.scene.control.TextInputDialog;

import de.uka.ilkd.key.core.fx.KeYMediatorF;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.exploration.ProofExplorationService;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * The four sequent context-menu items of the exploration extension, JavaFX port of the Swing
 * adapter {@code ExplorationExtension.adapter} (ExplorationExtension.java:59-73), which creates
 * the {@code AddFormulaToAntecedentAction}, {@code AddFormulaToSuccedentAction},
 * {@code EditFormulaAction} and {@code DeleteFormulaAction} for the clicked position.
 * <p>
 * The enablement mirrors the Swing action constructors:
 * <ul>
 * <li>both "Add formula …" items are always enabled,</li>
 * <li>"Edit formula" is enabled iff the position is not the whole sequent
 * ({@code !pos.isSequent()}),</li>
 * <li>"Delete formula" only for top-level formula occurrences inside the sequent.</li>
 * </ul>
 * The producers re-use the (Swing) {@link ProofExplorationService} with its
 * {@code soundAddition}/{@code applyChangeFormula}/{@code soundHide} operations.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing {@code promptForTerm} retry-loop (a modal input dialog that
 * re-opened itself until a well-typed term was entered, {@code ExplorationAction.java:35-65}) is
 * a single-shot {@link TextInputDialog} — malformed input or a sort mismatch abort the action.
 */
@NullMarked
final class ExplorationSequentMenuF {

    private ExplorationSequentMenuF() {
    }

    /**
     * Builds the four exploration items for the given goal and clicked position.
     *
     * @param mediator the mediator of the window (non-null when called by the host)
     * @param goal the goal whose sequent was clicked
     * @param pos the clicked position
     * @return the four menu items with the Swing enablement
     */
    static List<MenuItem> items(KeYMediatorF mediator, Goal goal, PosInSequent pos) {
        return List.of(
            item("Add formula to antecedent", true,
                e -> addFormula(mediator, goal, true)),
            item("Add formula to succedent", true,
                e -> addFormula(mediator, goal, false)),
            item("Edit formula", !pos.isSequent(),
                e -> editFormula(mediator, goal, pos)),
            item("Delete formula", deleteEnabled(pos),
                e -> deleteFormula(mediator, goal, pos)));
    }

    private static MenuItem item(String text, boolean enabled,
            EventHandler<ActionEvent> handler) {
        MenuItem item = new MenuItem(text);
        item.setDisable(!enabled);
        item.setOnAction(handler);
        return item;
    }

    /**
     * Swing {@code DeleteFormulaAction} constructor enablement
     * (DeleteFormulaAction.java:33-37): only enabled for top-level (non-null) occurrences.
     */
    private static boolean deleteEnabled(PosInSequent pos) {
        PosInOccurrence pio = pos.getPosInOccurrence();
        return pio != null && !pos.isSequent() && pio.isTopLevel();
    }

    /** Swing {@code AddFormulaToAntecedentAction}/{@code AddFormulaToSuccedentAction}. */
    private static void addFormula(KeYMediatorF mediator, Goal goal, boolean antecedent) {
        JTerm term = promptForTerm(goal, null);
        if (term == null) {
            return;
        }
        Services services = goal.proof().getServices();
        Node toBeSelected = new ProofExplorationService(goal.proof(), services)
                .soundAddition(goal, term, antecedent);
        mediator.getSelectionModel().setSelectedNode(toBeSelected);
    }

    /** Swing {@code EditFormulaAction} (EditFormulaAction.java:46-66). */
    private static void editFormula(KeYMediatorF mediator, Goal goal, PosInSequent pos) {
        if (pos.isSequent()) {
            return;
        }
        PosInOccurrence pio = pos.getPosInOccurrence();
        if (pio == null) {
            return;
        }
        Services services = goal.proof().getServices();
        // the cast mirrors the Swing EditFormulaAction (EditFormulaAction.java:53)
        JTerm term = (JTerm) pio.subTerm();
        SequentFormula sf = pio.sequentFormula();
        JTerm newTerm = promptForTerm(goal, term);
        if (newTerm == null || newTerm.equals(term)) {
            return;
        }
        JTerm formula = (JTerm) sf.formula();
        JTerm replaced = services.getTermBuilder().replace(formula, pio.posInTerm(), newTerm);
        Node toBeSelected = new ProofExplorationService(goal.proof(), services)
                .applyChangeFormula(goal, pio, formula, replaced);
        mediator.getSelectionModel().setSelectedNode(toBeSelected);
    }

    /** Swing {@code DeleteFormulaAction} (DeleteFormulaAction.java:42-55). */
    private static void deleteFormula(KeYMediatorF mediator, Goal goal, PosInSequent pos) {
        if (pos.isSequent()) {
            return;
        }
        PosInOccurrence pio = pos.getPosInOccurrence();
        if (pio == null || !pio.isTopLevel()) {
            return;
        }
        JTerm term = (JTerm) pio.subTerm();
        Services services = goal.proof().getServices();
        new ProofExplorationService(goal.proof(), services).soundHide(goal, pio, term);
    }

    /**
     * Single-shot formula prompt, FX port of Swing {@code ExplorationAction.promptForTerm}
     * (ExplorationAction.java:35-65). {@code null} aborts the action (cancel or malformed
     * input).
     *
     * @param goal the goal whose services/namespaces the parse shall use
     * @param term the existing term to pre-fill (and sort-check), or {@code null} for a fresh
     *        addition
     * @return the parsed term, or {@code null} when the user cancelled or the input was rejected
     */
    private static @Nullable JTerm promptForTerm(Goal goal, @Nullable JTerm term) {
        Services services = goal.proof().getServices();
        final String initialValue =
            term == null ? "" : LogicPrinter.quickPrintTerm(term, services);

        TextInputDialog dialog = new TextInputDialog(initialValue);
        dialog.setTitle("Exploration");
        dialog.setHeaderText("Input a formula:");
        dialog.setContentText("Term:");
        Optional<String> input = dialog.showAndWait();
        if (input.isEmpty()) {
            return null;
        }

        KeyIO io = new KeyIO(services);
        try {
            JTerm result = io.parseExpression(input.get());
            if (term != null && !result.sort().equals(term.sort())) {
                // KNOWN-SIMPLIFIED: the Swing prompt showed the sort-mismatch dialog and re-opened
                // the input dialog; the FX port is single-shot and aborts the action instead.
                showError("Sort mismatch",
                    String.format("%s is of sort %s, but we need a term of sort %s", result,
                        result.sort(), term.sort()));
                return null;
            }
            return result;
        } catch (BuildingException e) {
            // KNOWN-SIMPLIFIED: single-shot prompt — a malformed input aborts instead of looping.
            showError("Malformed input", e.getMessage());
            return null;
        }
    }

    private static void showError(String title, @Nullable String message) {
        Alert alert = new Alert(Alert.AlertType.ERROR);
        alert.setTitle(title);
        alert.setHeaderText(null);
        alert.setContentText(message == null ? "" : message);
        alert.showAndWait();
    }
}
