/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.infoview;

import java.nio.file.Path;
import javafx.scene.Scene;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.FxDriver;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Standalone driver for the {@link InfoViewF} (development scaffolding, see {@link FxDriver}):
 * shows the info view on the primary stage with its own {@link KeYSelectionModel} (no-op proof
 * binder) and loads a demo proof in the background via
 * {@link KeYEnvironment#load(Path)}.
 * <p>
 * System properties:
 * <ul>
 * <li>{@code key.fx.demo.sequent} — the {@code .key} file to load; without it, the view stays
 * empty,</li>
 * <li>{@code key.fx.demo.autoprove} — if set, run the automatic prover on the demo proof
 * (synchronously on the loader thread) before selecting it.</li>
 * </ul>
 * After the proof is selected, the self test {@link InfoViewF#verifyInfoView()} is executed and
 * logged.
 */
public final class InfoViewDriver implements FxDriver {

    private static final Logger LOGGER = LoggerFactory.getLogger(InfoViewDriver.class);

    @Override
    public void start(Stage stage) throws Exception {
        InfoViewF view = new InfoViewF();
        KeYSelectionModel selectionModel = new KeYSelectionModel((newProof, previousProof) -> {
            // no-op: this driver has no mediator behind the selection model
        });
        view.attach(selectionModel);

        Scene scene = new Scene(view, 600, 460);
        ThemeManager.getInstance().manage(scene);
        stage.setTitle("KeY · Info");
        stage.setScene(scene);
        stage.show();

        String demoFile = System.getProperty("key.fx.demo.sequent");
        if (demoFile == null || demoFile.isBlank()) {
            LOGGER.warn("No demo proof configured; set -Dkey.fx.demo.sequent=<file.key> to "
                + "populate the info view.");
            return;
        }
        boolean autoprove = System.getProperty("key.fx.demo.autoprove") != null;
        Thread loader = new Thread(
            () -> loadDemoProof(selectionModel, view, Path.of(demoFile), autoprove),
            "key-fx-infoview-demo-loader");
        loader.setDaemon(true);
        loader.start();
    }

    /**
     * Loads the demo proof, optionally runs the automatic prover, selects it in the model and
     * runs the view's self test.
     */
    private void loadDemoProof(KeYSelectionModel selectionModel, InfoViewF view, Path file,
            boolean autoprove) {
        try {
            long start = System.currentTimeMillis();
            KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file);
            Proof proof = env.getLoadedProof();
            LOGGER.info("Loaded demo proof '{}' from {} ({} ms)", proof.name(), file,
                System.currentTimeMillis() - start);
            if (autoprove) {
                long provingStart = System.currentTimeMillis();
                env.getProofControl().startAndWaitForAutoMode(proof);
                LOGGER.info("Auto mode finished in {} ms: openGoals={} closed={}",
                    System.currentTimeMillis() - provingStart, proof.openGoals().size(),
                    proof.closed());
            }
            selectionModel.setSelectedProof(proof);
            LOGGER.info("Info self test: {}", view.verifyInfoView());
        } catch (Exception e) {
            LOGGER.error("Failed to load demo proof {}", file, e);
        }
    }
}
