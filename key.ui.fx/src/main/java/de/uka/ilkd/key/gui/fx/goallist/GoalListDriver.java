/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.goallist;

import java.nio.file.Path;
import javafx.concurrent.Task;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.HBox;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.fx.KeYSelectionEvent;
import de.uka.ilkd.key.core.fx.KeYSelectionListener;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.FxDriver;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.StrategySettings;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Standalone {@link FxDriver} for the {@link GoalListViewF} (milestone M2): shows the goal list
 * with its own {@link KeYSelectionModel} and loads the demo proof named by the system property
 * {@code key.fx.demo.sequent} (a {@code .key} file) on a background thread via the core
 * {@link KeYEnvironment}, mirroring how the future mediator will route a loaded proof through the
 * selection model. If the system property {@code key.fx.goallist.autoprove} is set to a number,
 * that many automatic rule applications are run first (so the proof contains several nodes;
 * combined with {@code key.fx.goallist.select.root} the root becomes a closed inner node and a
 * click on the goal row performs a real selection change). The self-test
 * {@link GoalListViewF#verifyGoalList()} is run after the proof is displayed and reported on the
 * console.
 */
public final class GoalListDriver implements FxDriver {

    private static final Logger LOGGER = LoggerFactory.getLogger(GoalListDriver.class);

    @Override
    public void start(Stage stage) throws Exception {
        GoalListViewF view = new GoalListViewF();
        KeYSelectionModel model = new KeYSelectionModel((newProof, previousProof) -> {
            // no-op: a standalone driver has no mediator to bind the proof to
        });
        view.attach(model);

        Label header = new Label("Proof: none");
        header.getStyleClass().add("goal-list-header");
        header.setPadding(new Insets(6, 10, 6, 10));

        Label status = new Label("Ready.");
        HBox statusBar = new HBox(status);
        statusBar.getStyleClass().add("status-bar");

        BorderPane root = new BorderPane(view);
        root.setTop(header);
        root.setBottom(statusBar);

        // reports every selection change in the status bar and the log; this is the evidence that
        // clicking a goal row changes the selection
        model.addKeYSelectionListenerChecked(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> event) {
                status.setText(selectionText(model));
                LOGGER.info("GoalListDriver: {}", status.getText());
            }

            @Override
            public void selectedProofChanged(KeYSelectionEvent<Proof> event) {
                Proof proof = event.getSource().getSelectedProof();
                header.setText(proof == null ? "Proof: none" : "Proof: " + proof.name());
                // setSelectedProof fires only the proof event, but the model already auto-selects
                // the first open goal; reflect that selection here as well
                status.setText(selectionText(model));
                LOGGER.info("GoalListDriver: {}", status.getText());
            }

            private String selectionText(KeYSelectionModel model) {
                Node node = model.getSelectedNode();
                Goal goal = model.getSelectedGoal();
                return node == null ? "No selection."
                        : goal == null ? "Selected node #" + node.serialNr() + " (inner node)"
                                : "Selected goal #" + goal.node().serialNr() + " ("
                                    + (goal.isAutomatic() ? "automatic" : "interactive") + ")";
            }
        });

        stage.setTitle("KeY · Goal List");
        Scene scene = new Scene(root, 800, 500);
        // apply the KeY theme (key-light.css/key-dark.css) like MainWindowF does
        ThemeManager.getInstance().manage(scene);
        stage.setScene(scene);
        stage.show();

        startDemoProofLoad(model, view);
    }

    /**
     * Loads the demo proof on a background thread and routes it through the selection model
     * (whose handlers run on the FX thread), then runs the view's self-test.
     */
    private void startDemoProofLoad(KeYSelectionModel model, GoalListViewF view) {
        String file = System.getProperty("key.fx.demo.sequent");
        if (file == null || file.isBlank()) {
            LOGGER.warn("GoalListDriver: no demo proof, set -Dkey.fx.demo.sequent=<file.key>");
            return;
        }
        // optional: number of automatic rule applications to run before the goal list is shown,
        // so that the root becomes an inner node (verification affordance, like
        // key.fx.demo.autoprove of MainWindowF)
        final int autoSteps = readAutoSteps();
        Path location = Path.of(file);
        Task<KeYEnvironment<DefaultUserInterfaceControl>> loadTask = new Task<>() {
            @Override
            protected KeYEnvironment<DefaultUserInterfaceControl> call() throws Exception {
                KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(location);
                if (autoSteps > 0) {
                    Proof proof = env.getLoadedProof();
                    StrategySettings strategySettings =
                        proof.getSettings().getStrategySettings();
                    int originalSteps = strategySettings.getMaxSteps();
                    try {
                        // transient: restored below. Note that any change writes the user's
                        // proof-settings.json, hence the restore in the finally block.
                        strategySettings.setMaxSteps(autoSteps);
                        LOGGER.info("GoalListDriver: running auto mode with max {} steps",
                            autoSteps);
                        env.getProofControl().startAndWaitForAutoMode(proof);
                    } finally {
                        strategySettings.setMaxSteps(originalSteps);
                    }
                    LOGGER.info("GoalListDriver: auto mode finished, {} open goals",
                        proof.openGoals().size());
                }
                return env;
            }
        };
        loadTask.setOnSucceeded(event -> {
            Proof proof = loadTask.getValue().getLoadedProof();
            LOGGER.info("GoalListDriver: demo proof loaded {} ({} open goals)", location,
                proof.openGoals().size());
            // fires selectedProofChanged; onSucceeded runs on the FX thread like the future
            // mediator will
            model.setSelectedProof(proof);
            LOGGER.info("GoalList self test: {}", view.verifyGoalList());
            // Verification affordance: select the root node. Combined with
            // key.fx.goallist.autoprove>=1 the root is a closed inner node, so this clears the
            // goal selection and a subsequent interactive click on a goal row performs a real
            // selection change.
            if (System.getProperty("key.fx.goallist.select.root") != null) {
                model.setSelectedNode(proof.root());
            }
        });
        loadTask.setOnFailed(event -> {
            Throwable error = loadTask.getException();
            LOGGER.error("GoalListDriver: demo proof loading failed", error);
        });
        Thread loader = new Thread(loadTask, "fx-goallist-demo-loader");
        loader.setDaemon(true);
        loader.start();
    }

    /**
     * @return the number of automatic rule applications for the
     *         {@code key.fx.goallist.autoprove} property, or {@code 0} to show the proof as
     *         loaded
     */
    private static int readAutoSteps() {
        String steps = System.getProperty("key.fx.goallist.autoprove");
        if (steps == null || steps.isBlank()) {
            return 0;
        }
        try {
            return Math.max(0, Integer.parseInt(steps.trim()));
        } catch (NumberFormatException e) {
            LOGGER.warn("GoalListDriver: ignoring invalid key.fx.goallist.autoprove value {}",
                steps);
            return 0;
        }
    }
}
