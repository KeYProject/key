/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.fx;

import java.util.List;
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
import de.uka.ilkd.key.util.parsing.SyntaxErrorReporter;

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
 * The term prompt is a faithful port of the Swing {@code promptForTerm} retry-loop
 * ({@code ExplorationAction.java:35-65}): the input dialog re-opens itself until a well-typed
 * term of the required sort was entered — a sort mismatch shows the sort-mismatch dialog and
 * re-prompts ({@code ExplorationAction.java:46-53}), malformed input shows the error and
 * re-prompts ({@code ExplorationAction.java:54-57}); cancelling aborts the action. The dialog
 * and error surfaces sit behind the {@link PromptHandler} seam so the loop stays headlessly
 * unit-testable (the same pattern as {@code SequentMenuModelF}).
 */
@NullMarked
final class ExplorationSequentMenuF {

    private ExplorationSequentMenuF() {
    }

    /**
     * The input/error surface of the {@code promptForTerm} retry-loop (the Swing
     * {@code JOptionPane.showInputDialog}/{@code JOptionPane.showMessageDialog} calls of
     * {@code ExplorationAction.promptForTerm}, ExplorationAction.java:35-65): {@link #input}
     * returns the next user input, or {@code null} to cancel; the error arguments carry the
     * validation error of the previous input (both {@code null} on the first invocation), which
     * the real handler shows before re-opening the dialog — Swing shows the "Sort mismatch" /
     * "Malformed input" error dialog and re-opens the input dialog in the same order.
     */
    public interface PromptHandler {

        /**
         * Asks for the next formula input.
         *
         * @param initialValue the pre-filled input (the pretty-printed term being edited),
         *        constant across the retries
         * @param errorTitle the title of the previous input's error dialog ({@code null} on the
         *        first ask)
         * @param errorMessage the message of the previous input's error dialog ({@code null} on
         *        the first ask)
         * @return the entered text, or {@code null} to cancel the whole action
         */
        @Nullable
        String input(@Nullable String initialValue, @Nullable String errorTitle,
                @Nullable String errorMessage);
    }

    /** the production handler: shows the error alert, then opens the modal input dialog. */
    private static final PromptHandler DIALOG_HANDLER = (initialValue, errorTitle,
            errorMessage) -> {
        if (errorTitle != null) {
            showError(errorTitle, errorMessage);
        }
        TextInputDialog dialog = new TextInputDialog(initialValue == null ? "" : initialValue);
        dialog.setTitle("Exploration");
        dialog.setHeaderText("Input a formula:");
        dialog.setContentText("Term:");
        return dialog.showAndWait().orElse(null);
    };

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
     * Formula prompt with the Swing retry-loop, FX port of Swing {@code
     * ExplorationAction.promptForTerm} (ExplorationAction.java:35-65): the input dialog
     * re-opens itself until a well-typed term of the required sort was entered — a sort mismatch
     * shows the "Sort mismatch" dialog and re-prompts ({@code ExplorationAction.java:46-53}),
     * malformed input shows the "Malformed input" dialog and re-prompts
     * ({@code ExplorationAction.java:54-57}). {@code null} aborts the action (cancel).
     *
     * @param goal the goal whose services/namespaces the parse shall use
     * @param term the existing term to pre-fill (and sort-check), or {@code null} for a fresh
     *        addition
     * @return the parsed term, or {@code null} when the user cancelled
     */
    private static @Nullable JTerm promptForTerm(Goal goal, @Nullable JTerm term) {
        return promptForTerm(goal, term, DIALOG_HANDLER);
    }

    /**
     * The {@code promptForTerm} retry-loop with a pluggable {@link PromptHandler} (the test seam;
     * the production {@link #promptForTerm(Goal, JTerm)} uses the dialog handler): loops until
     * the input parses and matches the required sort, feeding each validation error back to the
     * handler, and returns {@code null} when the handler cancels.
     *
     * @param goal the goal whose services/namespaces the parse shall use
     * @param term the existing term to sort-check against, or {@code null} for a fresh addition
     * @param handler the input/error surface (dialog in production, scripted in the tests)
     * @return the parsed term, or {@code null} when the user cancelled
     */
    static @Nullable JTerm promptForTerm(Goal goal, @Nullable JTerm term, PromptHandler handler) {
        Services services = goal.proof().getServices();
        final String initialValue =
            term == null ? "" : LogicPrinter.quickPrintTerm(term, services);

        KeyIO io = new KeyIO(services);
        String errorTitle = null;
        String errorMessage = null;
        while (true) {
            String input = handler.input(initialValue, errorTitle, errorMessage);
            if (input == null) {
                // cancelled: abort the whole action like the Swing prompt (result == null)
                return null;
            }
            errorTitle = null;
            errorMessage = null;
            try {
                JTerm result = io.parseExpression(input);
                if (term != null && !result.sort().equals(term.sort())) {
                    // Swing parity: show the sort-mismatch dialog and re-open the input dialog
                    // (ExplorationAction.java:46-53)
                    errorTitle = "Sort mismatch";
                    errorMessage = String.format("%s is of sort %s, but we need a term of sort %s",
                        result, result.sort(), term.sort());
                    continue;
                }
                return result;
            } catch (BuildingException e) {
                // Swing parity: show the malformed-input dialog and re-open the input dialog
                // (ExplorationAction.java:54-57)
                errorTitle = "Malformed input";
                errorMessage = e.getMessage();
            } catch (SyntaxErrorReporter.ParserException e) {
                // FIXED-UPSTREAM: a syntactically malformed input raises the parser's
                // RuntimeException, which the Swing loop does not catch (it would abort with an
                // unhandled exception); the FX retry-loop treats it like any malformed input and
                // re-prompts
                errorTitle = "Malformed input";
                errorMessage = e.getMessage();
            }
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
