/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx.ui;

import javafx.application.Platform;
import javafx.geometry.Insets;
import javafx.scene.Scene;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.BorderPane;
import javafx.stage.Window;

import org.key_project.slicing.fx.ui.GraphvizDotExecutorF.Result;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Dialog that displays a rendering of the dependency graph, FX port of
 * {@code org.key_project.slicing.ui.PreviewDialog}: the DOT source is rendered by
 * {@link GraphvizDotExecutorF} (the graphviz {@code dot} binary) and the resulting image is
 * shown in an {@link ImageView} inside a scroll pane.
 * <p>
 * Deviations from the Swing original:
 * <ul>
 * <li>the render runs on a daemon thread instead of a {@code SwingWorker}; the dialog is only
 * opened once the render finished (the Swing original opens immediately with a
 * "Running dot on ... KB" label and swaps the image in when done) — the deterministic open
 * avoids a blank dialog flash and keeps the render off the FX thread,</li>
 * <li>the pan/zoom {@code PanZoomImageView} is not ported; the image is shown fit-to-width in a
 * {@link ScrollPane} (which provides the panning),</li>
 * <li>if the render fails (graphviz missing or {@code dot} error) the dialog falls back to the
 * DOT source text dialog ({@link SlicingLeftPanelF#showTextDialog}, the former stand-in seam)
 * prefixed with the error message.</li>
 * </ul>
 */
@NullMarked
public class PreviewDialogF extends javafx.stage.Stage {

    private static final Logger LOGGER = LoggerFactory.getLogger(PreviewDialogF.class);

    private PreviewDialogF(@Nullable Window owner, String title, Result result) {
        setTitle(title);
        if (owner != null) {
            initOwner(owner);
        }

        BorderPane root = new BorderPane();
        if (result.hasImage() && result.png() != null) {
            Image image = new Image(new java.io.ByteArrayInputStream(result.png()));
            ImageView view = new ImageView(image);
            view.setFitWidth(800);
            view.setFitHeight(600);
            view.setPreserveRatio(true);
            view.setSmooth(true);
            ScrollPane scroll = new ScrollPane(view);
            scroll.setPrefSize(820, 620);
            root.setCenter(scroll);
        } else {
            // documented fallback for an unavailable or failing graphviz installation: show the
            // error together with the DOT source (the previous stand-in behavior)
            Label error = new Label(
                "graphviz rendering failed (%s). Showing the DOT source instead.".formatted(
                    result.error() != null ? result.error() : "unknown error"));
            error.setWrapText(true);
            root.setTop(error);
        }

        Button closeButton = new Button("Close");
        closeButton.setOnAction(e -> close());
        closeButton.setDefaultButton(true);
        BorderPane.setMargin(closeButton, new Insets(10));
        root.setBottom(closeButton);

        setScene(new Scene(root, result.hasImage() ? 840 : 640,
            result.hasImage() ? 700 : 200));
    }

    /**
     * Renders the given DOT graph with graphviz and shows the result: an image dialog on
     * success, the documented DOT-source text fallback on failure (Swing
     * {@code new PreviewDialog(window, dot)}). The render runs on a daemon thread.
     *
     * @param owner owner window, may be {@code null}
     * @param dot graph to render (in DOT format)
     */
    public static void showDot(@Nullable Window owner, String dot) {
        Thread thread = new Thread(() -> {
            Result result = GraphvizDotExecutorF.renderPng(dot);
            LOGGER.info("dot render finished: image={} error={}", result.hasImage(),
                result.error());
            Platform.runLater(() -> {
                if (result.hasImage()) {
                    new PreviewDialogF(owner, "Preview", result).show();
                } else {
                    SlicingLeftPanelF.showTextDialog("Dependency graph (rendering failed)",
                        "graphviz rendering failed: %s%n%n%s".formatted(
                            result.error() != null ? result.error() : "unknown error", dot));
                }
            });
        }, "graphviz-dot-render");
        thread.setDaemon(true);
        thread.start();
    }
}
