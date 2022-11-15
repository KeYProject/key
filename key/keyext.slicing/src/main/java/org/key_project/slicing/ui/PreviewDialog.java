package org.key_project.slicing.ui;

import org.key_project.slicing.util.GraphvizDotExecutor;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import javax.imageio.ImageIO;
import javax.swing.*;
import javax.swing.border.EmptyBorder;
import java.awt.*;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.awt.image.BufferedImage;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;

/**
 * Dialog that displays a rendering of the dependency graph.
 * Requires that graphviz (dot) is installed on the system.
 *
 * @author Arne Keller
 */
public class PreviewDialog extends JDialog implements WindowListener {
    private final transient GraphvizDotExecutor worker;

    /**
     * Create a new preview dialog to show the graph provided in DOT syntax.
     * Automatically starts dot, displays resulting image once complete.
     *
     * @param window parent window
     * @param dot graph in DOT format
     */
    public PreviewDialog(Window window, String dot) {
        super(window, "Preview");
        setLayout(new BorderLayout());
        var label = new JLabel(
            String.format("Running dot on %d KB of graph data...", dot.length() / 1024));
        label.setBorder(new EmptyBorder(10, 10, 10, 10));
        getContentPane().add(label, BorderLayout.NORTH);

        worker = new GraphvizDotExecutor(dot, window, this);
        worker.execute();

        pack();
        setLocationRelativeTo(window);
        setVisible(true);
        addWindowListener(this);
    }

    @Override
    public void windowClosing(WindowEvent e) {
        if (worker != null) {
            worker.cancel(true);
        }
    }

    @Override
    public void windowOpened(WindowEvent e) {

    }

    @Override
    public void windowClosed(WindowEvent e) {

    }

    @Override
    public void windowIconified(WindowEvent e) {

    }

    @Override
    public void windowDeiconified(WindowEvent e) {

    }

    @Override
    public void windowActivated(WindowEvent e) {

    }

    @Override
    public void windowDeactivated(WindowEvent e) {

    }
}
