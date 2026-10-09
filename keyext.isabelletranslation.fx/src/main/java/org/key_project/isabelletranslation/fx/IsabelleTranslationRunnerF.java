/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.util.ArrayList;
import java.util.List;
import javafx.stage.Window;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.isabelletranslation.automation.IsabelleProblem;
import org.key_project.isabelletranslation.translation.IllegalFormulaException;
import org.key_project.isabelletranslation.translation.IsabelleTranslator;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Runs the Isabelle sequent translation of the context-menu actions of
 * {@link IsabelleTranslationExtensionF} and presents the resulting theories in a dialog.
 * <p>
 * <b>KNOWN-SIMPLIFIED:</b> the Swing actions hand the generated theories to the external Isabelle
 * solver and show a progress/model dialog (IsabelleTranslationAction.solveGoals,
 * IsabelleTranslationAction.java:47-81). The FX port stops after the translation itself
 * ({@link IsabelleTranslator#translateProblem(Goal)}, the exact same translation machinery the
 * Swing action uses) and displays the theory text. The translation is executed on a background
 * thread so the heavy handler loading never blocks the FX main thread, and the class-loading of
 * the scala-isabelle backend is avoided entirely (it is only needed by the launcher).
 */
@NullMarked
final class IsabelleTranslationRunnerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslationRunnerF.class);

    private IsabelleTranslationRunnerF() {
    }

    /**
     * Translates the given goal into an Isabelle theory and shows the result.
     *
     * @param goal the goal to translate
     * @param owner the dialog owner, may be {@code null}
     */
    static void translateGoal(Goal goal, @Nullable Window owner) {
        translate(List.of(goal), owner);
    }

    /**
     * Translates all open goals of the proof of the given goal and shows the results.
     *
     * @param goal a goal of the proof whose open goals shall be translated
     * @param owner the dialog owner, may be {@code null}
     */
    static void translateAllGoals(Goal goal, @Nullable Window owner) {
        translate(goal.proof().openGoals().stream().toList(), owner);
    }

    private static void translate(List<Goal> goals, @Nullable Window owner) {
        if (goals.isEmpty()) {
            return;
        }
        Goal first = goals.get(0);
        Services services = first.proof().getServices();
        if (services == null) {
            LOGGER.warn("No proof services available - cannot translate to Isabelle");
            return;
        }
        IsabelleTranslator translator = new IsabelleTranslator(services);
        Thread thread = new Thread(() -> {
            List<IsabelleTranslationDialogF.Entry> entries = new ArrayList<>();
            for (Goal goal : goals) {
                entries.add(translateGoal(translator, goal));
            }
            FxUtil.runLater(() -> IsabelleTranslationDialogF.show(owner, entries));
        }, "IsabelleTranslationThread");
        thread.setDaemon(true);
        thread.start();
    }

    private static IsabelleTranslationDialogF.Entry translateGoal(IsabelleTranslator translator,
            Goal goal) {
        try {
            // Swing IsabelleTranslationAction.java:53-61: translateProblem throws
            // IllegalFormulaException for untranslatable formulas; the problem still enters the
            // result list so the user sees which goals failed.
            IsabelleProblem problem = translator.translateProblem(goal);
            return new IsabelleTranslationDialogF.Entry(problem.getName(), problem.getPreamble(),
                problem.getTranslation(), null);
        } catch (IllegalFormulaException e) {
            LOGGER.debug("Translation of {} failed", goal, e);
            return new IsabelleTranslationDialogF.Entry("Goal " + goal.node().serialNr(), null,
                null,
                e.getMessage());
        }
    }
}
