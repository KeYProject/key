/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.isabelletranslation.fx;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import javafx.scene.control.Alert;
import javafx.stage.Window;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.isabelletranslation.IsabelleTranslationSettings;
import org.key_project.isabelletranslation.automation.IsabelleLauncher;
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
 * {@link IsabelleTranslationExtensionF} and hands the generated theories to the external Isabelle
 * solver — JavaFX port of {@code IsabelleTranslationAction.solveGoals}
 * (IsabelleTranslationAction.java:47-81): the translation runs on a background thread
 * ("IsabelleLauncherThread"), then an {@link IsabelleLauncher} checks the theories with the
 * configured Isabelle installation and an {@link IsabelleLauncherProgressDialogMediatorF} presents
 * the progress dialog. When the launch fails (Isabelle not installed / unusable, or the
 * translation files could not be written), the progress dialog is discarded and a "Launch failed!"
 * error alert is shown (Swing JOptionPane error message); the generated theories remain
 * accessible in the plain translation dialog (a small FX improvement over the Swing error path,
 * which discards them).
 * <p>
 * The scala-isabelle backend classes are loaded lazily: only the actual solver execution
 * ({@code IsabelleResourceController.init()} inside {@code IsabelleLauncher.launch}) touches them,
 * so the FX port can always run the translation without the backend being initialized.
 */
@NullMarked
final class IsabelleTranslationRunnerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(IsabelleTranslationRunnerF.class);

    private IsabelleTranslationRunnerF() {
    }

    /**
     * Translates the given goal into an Isabelle theory and checks the translation with the
     * Isabelle solver.
     *
     * @param goal the goal to translate
     * @param owner the dialog owner, may be {@code null}
     */
    static void translateGoal(Goal goal, @Nullable Window owner) {
        translate(List.of(goal), owner);
    }

    /**
     * Translates all open goals of the proof of the given goal and checks the translations with
     * the Isabelle solver.
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
            List<IsabelleProblem> problems = new ArrayList<>();
            List<IsabelleTranslationDialogF.Entry> entries = new ArrayList<>();
            for (Goal goal : goals) {
                translateGoal(translator, goal, problems, entries);
            }
            if (problems.stream().noneMatch(IsabelleProblem::hasTranslation)) {
                // Swing IsabelleTranslationAction.solveGoals queues the untranslatable problems
                // as well (their solvers then fail); booting Isabelle for a list of only failed
                // translations is pointless, so the failures are shown directly.
                FxUtil.runLater(() -> IsabelleTranslationDialogF.show(owner, entries));
                return;
            }
            // Swing IsabelleTranslationAction.java:63-68: the launcher runs on its own thread and
            // drives the progress dialog through the mediator listener; launch blocks until all
            // solvers have finished (or failed).
            IsabelleTranslationSettings settings = IsabelleTranslationSettings.getInstance();
            IsabelleLauncher launcher = new IsabelleLauncher(settings);
            IsabelleLauncherProgressDialogMediatorF progressDialogMediator =
                new IsabelleLauncherProgressDialogMediatorF(owner, first.proof(), launcher);
            launcher.addListener(progressDialogMediator);
            try {
                launcher.launch(problems, settings.getTimeout(), 1);
            } catch (IOException e) {
                // Thrown when Isabelle was not found (IsabelleNotFoundException) or translation
                // files could not be written (Swing IsabelleTranslationAction.java:69-73)
                progressDialogMediator.discardEvent();
                FxUtil.runLater(() -> {
                    Alert alert = new Alert(Alert.AlertType.ERROR, e.getMessage(),
                        javafx.scene.control.ButtonType.OK);
                    alert.setTitle("Launch failed!");
                    alert.setHeaderText("Launch failed!");
                    if (owner != null) {
                        alert.initOwner(owner);
                    }
                    alert.showAndWait();
                    // keep the pre-port FX capability: the generated theories stay accessible
                    // even when the solver cannot run
                    IsabelleTranslationDialogF.show(owner, entries);
                });
            }
        }, "IsabelleLauncherThread");
        thread.setDaemon(true);
        thread.start();
    }

    /**
     * Translates a single goal into a problem; untranslatable formulas become a problem without
     * translation so the solver reports the failure (Swing IsabelleTranslationAction.java:53-61),
     * and the failure text enters the entries list for the theory dialog.
     */
    private static void translateGoal(IsabelleTranslator translator, Goal goal,
            List<IsabelleProblem> problems, List<IsabelleTranslationDialogF.Entry> entries) {
        try {
            IsabelleProblem problem = translator.translateProblem(goal);
            problems.add(problem);
            entries.add(new IsabelleTranslationDialogF.Entry(problem.getName(),
                problem.getPreamble(), problem.getTranslation(), null));
        } catch (IllegalFormulaException e) {
            LOGGER.debug("Translation of {} failed", goal, e);
            problems.add(new IsabelleProblem(goal, e));
            entries.add(new IsabelleTranslationDialogF.Entry("Goal " + goal.node().serialNr(),
                null, null, e.getMessage()));
        }
    }
}
