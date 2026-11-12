/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.strategy;

import java.beans.PropertyChangeEvent;
import java.nio.file.Path;
import javafx.geometry.Insets;
import javafx.geometry.Pos;
import javafx.geometry.Rectangle2D;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.Separator;
import javafx.scene.layout.BorderPane;
import javafx.scene.layout.VBox;
import javafx.stage.Screen;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.FxDriver;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.StrategySettings;

import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Standalone development driver for the {@link StrategySelectionViewF}: shows the strategy view
 * together with a status label, backed by an own {@link KeYSelectionModel} without a mediator
 * behind it. The demo proof named by the system property {@code key.fx.demo.sequent} is loaded on
 * a background thread via the core {@link KeYEnvironment} and selected in the model, so the view
 * displays and writes through the settings of a live proof. After the proof is displayed the
 * driver runs the view's self test {@code verifyStrategyView()} and logs its report.
 */
public final class StrategySelectionDriver implements FxDriver {

    private static final Logger LOGGER = LoggerFactory.getLogger(StrategySelectionDriver.class);

    private final KeYSelectionModel selectionModel =
        new KeYSelectionModel((newProof, previousProof) -> {
            // no-op: the driver runs without a mediator behind its selection model
        });
    private final StrategySelectionViewF view = new StrategySelectionViewF();
    private final Label status = new Label("Loading demo proof ...");
    private final Label settingsMirror = new Label();

    @Override
    public void start(Stage stage) throws Exception {
        stage.setTitle("KeY · Strategy");

        status.getStyleClass().add("strategy-status");
        status.setAlignment(Pos.CENTER_LEFT);
        settingsMirror.getStyleClass().add("strategy-status");
        settingsMirror.setAlignment(Pos.CENTER_LEFT);
        VBox bottom = new VBox(4, new Separator(), status, settingsMirror);
        bottom.setPadding(new Insets(2, 8, 4, 8));

        BorderPane root = new BorderPane();
        root.setCenter(view);
        root.setBottom(bottom);

        Scene scene = new Scene(root, 900, 760);
        ThemeManager.getInstance().manage(scene);
        stage.setScene(scene);
        stage.show();
        // Without a window manager (headless Xvnc verification) the platform places the stage
        // off-screen; center it on the primary screen after the platform placement.
        Rectangle2D bounds = Screen.getPrimary().getVisualBounds();
        stage.setX(bounds.getMinX() + Math.max(0, (bounds.getWidth() - scene.getWidth()) / 2));
        stage.setY(bounds.getMinY() + Math.max(0, (bounds.getHeight() - scene.getHeight()) / 2));

        view.attach(selectionModel);

        String demoPath = System.getProperty("key.fx.demo.sequent");
        if (demoPath == null || demoPath.isBlank()) {
            status.setText("No demo proof given; pass -Dkey.fx.demo.sequent=<file.key>");
            LOGGER.warn("No demo proof given (system property key.fx.demo.sequent is unset)");
            return;
        }
        Thread loader =
            new Thread(() -> loadDemoProof(Path.of(demoPath)), "strategy-driver-loader");
        loader.setDaemon(true);
        loader.start();
    }

    /**
     * Loads the demo proof on the calling (background) thread and selects it in the model, then
     * runs the view's self test.
     *
     * @param path the location of the demo problem
     */
    private void loadDemoProof(Path path) {
        try {
            KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(path);
            Proof proof = env.getLoadedProof();
            FxUtil.runLater(() -> {
                selectionModel.setSelectedProof(proof);
                status.setText("Proof: " + proof.name() + " · " + env.getServices().getProfile()
                        .displayName());
                observeStrategySettings(proof);
                LOGGER.info("Strategy self test: {}", view.verifyStrategyView());
            });
        } catch (Exception e) {
            LOGGER.error("Failed to load demo proof {}", path, e);
            FxUtil.runLater(() -> status.setText("Failed to load demo proof: " + e));
        }
    }

    /**
     * Mirrors the strategy settings of the given proof into the second status line and the log,
     * whenever a setting changes. This makes the write-through of the view observable from the
     * outside (the mirror is updated on every user edit of the widgets).
     *
     * @param proof the proof whose strategy settings are observed
     */
    private void observeStrategySettings(Proof proof) {
        StrategySettings settings = proof.getSettings().getStrategySettings();
        settings.addPropertyChangeListener(this::logStrategySetting);
        updateSettingsMirror();
    }

    /**
     * Logs a strategy settings change and refreshes the settings mirror line.
     *
     * @param event the property change event of {@link StrategySettings}
     */
    private void logStrategySetting(PropertyChangeEvent event) {
        FxUtil.runLater(() -> {
            LOGGER.info("Strategy setting changed: {} = {} (was {})", event.getPropertyName(),
                event.getNewValue(), event.getOldValue());
            updateSettingsMirror();
        });
    }

    /**
     * Refreshes the settings mirror line from the currently selected proof.
     */
    private void updateSettingsMirror() {
        Proof proof = selectionModel.getSelectedProof();
        if (proof == null) {
            settingsMirror.setText("");
            return;
        }
        StrategySettings settings = proof.getSettings().getStrategySettings();
        settingsMirror.setText("Settings: maxSteps=" + settings.getMaxSteps() + " · strategy="
            + settings.getStrategy() + " · timeout=" + settings.getTimeout() + " ms");
    }
}
