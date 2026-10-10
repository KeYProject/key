/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.sourceview;

import java.nio.file.Path;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.layout.BorderPane;
import javafx.stage.Stage;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.core.fx.KeYSelectionModel;
import de.uka.ilkd.key.gui.fx.FxDriver;
import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.proof.Proof;

import org.key_project.util.javafx.FxUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Standalone driver for the source view (milestone M2), used with the {@code key.fx.driver} hook
 * of {@code MainApplication} for per-view verification without the full main window (same
 * pattern as the sequent view spike). Shows a single {@link SourceViewF} with a header label and
 * a local {@link KeYSelectionModel} (the {@code ProofBinder} seam is a no-op, since no mediator
 * is involved).
 * <p>
 * If the system property {@code key.fx.demo.sequent} names a problem file, it is loaded with the
 * core {@link KeYEnvironment} on a background thread; the loaded proof is routed through the
 * selection model (which drives the view), and the same file is registered as the
 * {@link SourceViewF#setFallbackSourceFile(Path) fallback} so that pure {@code .key} problems
 * without Java source (e.g. the Agatha example) still display their content. After the first
 * content load the driver logs the view's self-test via {@code Source self test: ...}.
 */
public final class SourceViewDriver implements FxDriver {

    public static final Logger LOGGER = LoggerFactory.getLogger(SourceViewDriver.class);

    @Override
    public void start(Stage stage) throws Exception {
        SourceViewF view = new SourceViewF();

        String demoFile = System.getProperty("key.fx.demo.sequent");
        if (demoFile != null && !demoFile.isBlank()) {
            // pure .key problems carry no Java source; show the problem file itself in that case
            view.setFallbackSourceFile(Path.of(demoFile));
        }

        // own selection model for the driver; the mediator seam is a no-op here
        KeYSelectionModel selectionModel = new KeYSelectionModel((newProof, previousProof) -> {
        });
        view.attach(selectionModel);
        view.setOnContentLoaded(() -> LOGGER.info("Source self test: {}", view.verifySourceView()));

        Label header = new Label("No source loaded");
        header.getStyleClass().add("source-view-header");
        header.textProperty().bind(view.headerTextProperty());
        BorderPane.setMargin(header, new Insets(0));
        BorderPane root = new BorderPane(view, header, null, null, null);

        Scene scene = new Scene(root, 1100, 750);
        ThemeManager.getInstance().manage(scene);
        stage.setTitle("KeY · Source");
        stage.setScene(scene);
        stage.show();

        if (demoFile == null || demoFile.isBlank()) {
            LOGGER.info("No key.fx.demo.sequent set; the source view stays empty. "
                + "Start with -Dkey.fx.demo.sequent=<file.key> to try the source view.");
            return;
        }

        Path location = Path.of(demoFile);
        Thread loader = new Thread(() -> {
            try {
                KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(location);
                Proof proof = env.getLoadedProof();
                LOGGER.info("Demo proof loaded: {}",
                    proof != null ? proof.name() : "(no proof in " + location + ")");
                FxUtil.runLater(() -> selectionModel.setSelectedProof(proof));
            } catch (Exception e) {
                LOGGER.error("Demo proof loading failed", e);
                // no proof -> the view keeps/returns to the "No source loaded" placeholder
                FxUtil.runLater(() -> selectionModel.setSelectedProof(null));
            }
        }, "fx-source-demo-loader");
        loader.setDaemon(true);
        loader.start();
    }
}
