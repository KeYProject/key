package org.key_project.slicing.util;

import org.key_project.slicing.ui.PanZoomImageView;
import org.key_project.slicing.ui.PreviewDialog;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.imageio.ImageIO;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import java.awt.*;
import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;

public class GraphvizDotExecutor extends SwingWorker<Void, Void> {
    private static final Logger LOGGER = LoggerFactory.getLogger(GraphvizDotExecutor.class);

    private static String GRAPHVIZ_DOT_EXECUTABLE = "dot";
    private static boolean GRAPHVIZ_DOT_INSTALLATION_CHECKED = false;
    private static boolean GRAPHVIZ_DOT_INSTALLED = false;

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
     * The preview dialog.
     */
    private final PreviewDialog dialog;
    /**
     * The main window (used to set the relative position of the dialog).
     */
    private final Window window;

    /**
     * Tries to execute <code>dot -V</code> or <code>dot.exe -V</code>.
     * If either works, dot is available.
     */
    private static void checkDotInstallation() {
        if (checkDotExecutable("dot")) {
            return;
        }
        checkDotExecutable("dot.exe");
    }

    private static boolean checkDotExecutable(String executableName) {
        try {
            Process process = new ProcessBuilder(executableName, "-V").start();
            if (process.waitFor() == 0) {
                GRAPHVIZ_DOT_INSTALLED = true;
                GRAPHVIZ_DOT_EXECUTABLE = executableName;
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
        if (!GRAPHVIZ_DOT_INSTALLATION_CHECKED) {
            checkDotInstallation();
        }
        return GRAPHVIZ_DOT_INSTALLED;
    }

    public GraphvizDotExecutor(String dot, Window window, PreviewDialog dialog) {
        this.dot = dot;
        this.window = window;
        this.dialog = dialog;
    }

    @Override
    protected Void doInBackground() {
        Process process = null;
        try {
            var input = dot.getBytes(StandardCharsets.UTF_8);
            LOGGER.info("starting dot with {} MB of graph data", input.length / 1024 / 1024);
            process = new ProcessBuilder(GRAPHVIZ_DOT_EXECUTABLE, "-Tpng").start();
            var stdin = process.getOutputStream();
            stdin.write(input);
            stdin.close();
            var outStream = process.getInputStream();
            var errStream = process.getErrorStream();
            var output = new ByteArrayOutputStream();
            var stderr = new ByteArrayOutputStream();
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
            process.destroy();
            Thread.currentThread().interrupt();
        }
        return null;
    }

    @Override
    protected void done() {
        super.done();
        if (img != null) {
            dialog.getContentPane().removeAll();
            PanZoomImageView pziv = new PanZoomImageView(img, 800, 600);
            pziv.setPreferredSize(new Dimension(800, 600));
            dialog.getContentPane().add(pziv, BorderLayout.CENTER);
        } else if (error != null) {
            var label = new JLabel(error);
            label.setBorder(new EmptyBorder(0, 10, 10, 10));
            dialog.getContentPane().add(label, BorderLayout.SOUTH);
        } else {
            var label = new JLabel("Unknown error occurred when executing dot.");
            label.setBorder(new EmptyBorder(0, 10, 10, 10));
            dialog.getContentPane().add(label, BorderLayout.SOUTH);
        }
        dialog.pack();
        dialog.setLocationRelativeTo(window);
    }
}
