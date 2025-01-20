/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.util;

import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import javax.imageio.ImageIO;
import javax.swing.*;

import org.key_project.slicing.SlicingSettings;
import org.key_project.slicing.SlicingSettingsProvider;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Provides facilities to launch graphviz, forward the graph input data and parse the resulting
 * image.
 *
 * @author Arne Keller
 */
public class GraphvizDotExecutor extends SwingWorker<GraphvizResult, Void> {
    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(GraphvizDotExecutor.class);

    /**
     * Whether availability of dot has already been checked.
     */
    private static boolean graphvizDotInstallationChecked = false;
    /**
     * Whether the dot executable at the provided path works.
     */
    private static boolean graphvizDotInstalled = false;

    /**
     * Execution error.
     */
    private String error;
    /**
     * The rendered graph.
     */
    private BufferedImage img;
    /**
     * Graph to be rendered (dot format).
     */
    private final String dot;

    /**
     * Construct a new graphviz executor given the provided input graph.
     *
     * @param dot graph to render (in DOT format)
     */
    public GraphvizDotExecutor(String dot) {
        this.dot = dot;
    }

    /**
     * Tries to execute <code>dot -V</code>, <code>dot.exe -V</code> or another dot executable
     * (depending on the settings).
     * If the call works, dot is available.
     */
    private static void checkDotInstallation() {
        graphvizDotInstallationChecked = true;
        SlicingSettings ss = SlicingSettingsProvider.getSlicingSettings();
        checkDotExecutable(ss.getDotExecutable());
    }

    private static boolean checkDotExecutable(String executableName) {
        try {
            Process process = new ProcessBuilder(executableName, "-V").start();
            if (process.waitFor() == 0) {
                graphvizDotInstalled = true;
                return true;
            }
        } catch (IOException | InterruptedException e) {
            return false;
        }
        return false;
    }

    /**
     * Checks whether graphviz is installed.
     *
     * @return whether this class is usable
     */
    public static boolean isDotInstalled() {
        if (!graphvizDotInstallationChecked) {
            checkDotInstallation();
        }
        return graphvizDotInstalled;
    }

    @Override
    protected GraphvizResult doInBackground() {
        SlicingSettings ss = SlicingSettingsProvider.getSlicingSettings();
        Process process = null;
        try {
            byte[] input = dot.getBytes(StandardCharsets.UTF_8);
            LOGGER.info("starting dot with {} MB of graph data", input.length / 1024 / 1024);
            process = new ProcessBuilder(ss.getDotExecutable(), "-Tpng").start();
            OutputStream stdin = process.getOutputStream();
            stdin.write(input);
            stdin.close();
            InputStream outStream = process.getInputStream();
            InputStream errStream = process.getErrorStream();
            ByteArrayOutputStream output = new ByteArrayOutputStream();
            ByteArrayOutputStream stderr = new ByteArrayOutputStream();
            byte[] buffer = new byte[65536];
            while (process.isAlive()
                    || outStream.available() > 0 || errStream.available() > 0) {
                while (outStream.available() > 0) {
                    int res = outStream.read(buffer);
                    if (res > 0) {
                        output.write(buffer, 0, res);
                    }
                }
                while (errStream.available() > 0) {
                    int res2 = errStream.read(buffer);
                    if (res2 > 0) {
                        stderr.write(buffer, 0, res2);
                    }
                }
                Thread.sleep(10);
            }
            if (process.exitValue() != 0) {
                error = stderr.toString();
            } else {
                img = ImageIO.read(new ByteArrayInputStream(output.toByteArray()));
            }
        } catch (IOException e) {
            error = e.getMessage();
        } catch (InterruptedException e) {
            LOGGER.info("stopping dot");
            error = "dot interrupted";
            process.destroy();
            Thread.currentThread().interrupt();
        }
        if (img != null) {
            return GraphvizResult.makeImage(img);
        } else {
            return GraphvizResult.makeError(error);
        }
    }
}
