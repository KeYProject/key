/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx.ui;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;

import org.key_project.slicing.SlicingSettings;
import org.key_project.slicing.SlicingSettingsProvider;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Renders a graph in DOT format to a PNG image by launching the graphviz {@code dot} binary
 * (non-Swing FX port of {@code org.key_project.slicing.util.GraphvizDotExecutor}):
 * the DOT source is piped into {@code dot -Tpng} through stdin and the resulting PNG bytes are
 * handed to the FX {@link javafx.scene.image.Image} of {@link PreviewDialogF}.
 * <p>
 * Deviations from the Swing original (which is an AWT/Swing {@code SwingWorker} producing a
 * {@code BufferedImage} via {@code javax.imageio.ImageIO}):
 * <ul>
 * <li>the render is a plain blocking method (no Swing worker); callers must invoke it off the
 * JavaFX application thread and marshall the dialog update back with
 * {@code Platform.runLater} (the callers in {@link SlicingLeftPanelF} and
 * {@code SlicingExtensionF#showGraphItem} do exactly that),</li>
 * <li>the {@code dot} availability check is re-run on every render instead of being cached in a
 * static field: the executable path is a user setting that may change between renders, and the
 * {@code key.fx.verify.slicing} harness has to exercise the not-installed fallback within a
 * single app run,</li>
 * <li>the image is kept as raw PNG bytes ({@code javafx.scene.image.Image} accepts a byte
 * array); no AWT image types are involved.</li>
 * </ul>
 * If {@code dot} is not installed (or fails), {@link #renderPng} returns an error result and the
 * callers fall back to showing the DOT source text (the documented fallback, exercised by the
 * verify harness even when {@code dot} is present).
 *
 * @author Alexander Weigl (FX port)
 * @author Arne Keller (Swing original)
 */
@NullMarked
public final class GraphvizDotExecutorF {

    private static final Logger LOGGER = LoggerFactory.getLogger(GraphvizDotExecutorF.class);

    private GraphvizDotExecutorF() {
    }

    /**
     * The outcome of a {@code dot} invocation (the FX counterpart of the Swing
     * {@code GraphvizResult}).
     *
     * @param png the rendered PNG image data, {@code null} if an error occurred
     * @param error the error message, {@code null} if an image was rendered
     */
    public record Result(byte @Nullable [] png, @Nullable String error) {

        /** @return whether this result contains a rendered image */
        public boolean hasImage() {
            return png != null;
        }

        /** @return whether this result indicates an error */
        public boolean hasError() {
            return error != null;
        }

        /**
         * @return whether the rendered data carries the PNG magic bytes (8-byte signature
         *         {@code 89 50 4E 47 0D 0A 1A 0A})
         */
        public boolean isPng() {
            return png != null && png.length > 8 && png[0] == (byte) 0x89 && png[1] == 0x50
                    && png[2] == 0x4E && png[3] == 0x47 && png[4] == 0x0D && png[5] == 0x0A
                    && png[6] == 0x1A && png[7] == 0x0A;
        }
    }

    /**
     * Checks whether the configured {@code dot} executable works (Swing
     * {@code GraphvizDotExecutor.isDotInstalled}): runs {@code <dot> -V}.
     * <p>
     * Unlike the Swing original this is not cached — see the class javadoc.
     *
     * @return whether graphviz rendering is available
     */
    public static boolean isDotInstalled() {
        String executable = executablePath();
        if (executable.isBlank()) {
            return false;
        }
        try {
            Process process = new ProcessBuilder(executable, "-V").start();
            int exit = process.waitFor();
            process.destroyForcibly();
            return exit == 0;
        } catch (IOException | InterruptedException e) {
            return false;
        }
    }

    /**
     * Renders the given DOT graph to a PNG image (Swing
     * {@code GraphvizDotExecutor.doInBackground}). <b>Blocking</b> — call off the FX thread.
     *
     * @param dot graph to render (in DOT format)
     * @return the render result (image or error)
     */
    public static Result renderPng(String dot) {
        String executable = executablePath();
        byte[] input = dot.getBytes(StandardCharsets.UTF_8);
        LOGGER.info("starting dot ({}) with {} KB of graph data", executable, input.length / 1024);
        Process[] processHolder = new Process[1];
        try {
            processHolder[0] = new ProcessBuilder(executable, "-Tpng").start();
            Process process = processHolder[0];
            try (OutputStream stdin = process.getOutputStream()) {
                stdin.write(input);
            }
            ByteArrayOutputStream stdout = new ByteArrayOutputStream();
            ByteArrayOutputStream stderr = new ByteArrayOutputStream();
            Thread errDrain = Thread.ofPlatform().daemon().name("dot-stderr-drain").start(() -> {
                try (InputStream errStream = process.getErrorStream()) {
                    errStream.transferTo(stderr);
                } catch (IOException e) {
                    // the drain thread terminates together with the process
                }
            });
            try (InputStream outStream = process.getInputStream()) {
                outStream.transferTo(stdout);
            }
            int exit = process.waitFor();
            errDrain.join(5000);
            if (exit != 0) {
                return new Result(null, stderr.toString(StandardCharsets.UTF_8));
            }
            byte[] png = stdout.toByteArray();
            if (png.length == 0) {
                return new Result(null, "dot produced no image data");
            }
            return new Result(png, null);
        } catch (IOException e) {
            LOGGER.info("failed to run dot ({})", executable, e);
            return new Result(null, String.valueOf(e.getMessage()));
        } catch (InterruptedException e) {
            LOGGER.info("stopping dot");
            if (processHolder[0] != null) {
                processHolder[0].destroyForcibly();
            }
            Thread.currentThread().interrupt();
            return new Result(null, "dot interrupted");
        }
    }

    /**
     * @return the configured dot executable path (Swing
     *         {@code SlicingSettings.getDotExecutable}, which falls back to {@code dot})
     */
    private static String executablePath() {
        SlicingSettings settings = SlicingSettingsProvider.getSlicingSettings();
        return settings.getDotExecutable();
    }
}
