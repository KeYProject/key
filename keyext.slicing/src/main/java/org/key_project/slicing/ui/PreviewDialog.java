/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.awt.event.WindowEvent;
import java.awt.event.WindowListener;
import java.util.concurrent.ExecutionException;
import javax.swing.*;
import javax.swing.border.EmptyBorder;

import org.key_project.slicing.util.GraphvizDotExecutor;
import org.key_project.slicing.util.GraphvizResult;

/**
 * Dialog that displays a rendering of the dependency graph.
 * Requires that graphviz (dot) is installed on the system.
 *
 * @author Arne Keller
 */
public class PreviewDialog extends JDialog implements WindowListener {
    /**
     * Graphviz executor.
     */
    private final transient GraphvizDotExecutor worker;
    /**
     * Parent window of this dialog.
     */
    private final Window window;

    /**
     * Create a new preview dialog to show the graph provided in DOT syntax.
     * Automatically starts dot, displays resulting image once complete.
     *
     * @param window parent window
     * @param dot graph in DOT format
     */
    public PreviewDialog(Window window, String dot) {
        super(window, "Preview");

        this.window = window;

        getContentPane().setLayout(new BorderLayout());
        JLabel label = new JLabel(
            String.format("Running dot on %d KB of graph data...", dot.length() / 1024));
        label.setBorder(new EmptyBorder(10, 10, 10, 10));

        JPanel buttonPane = new JPanel();
        JButton stop = new JButton("Cancel");
        stop.addActionListener(
            e -> dispatchEvent(new WindowEvent(this, WindowEvent.WINDOW_CLOSING)));
        buttonPane.add(stop);

        add(label, BorderLayout.NORTH);
        add(buttonPane, BorderLayout.CENTER);

        worker = new GraphvizDotExecutor(dot);
        worker.execute();
        worker.addPropertyChangeListener(event -> {
            if ("state".equals(event.getPropertyName())
                    && SwingWorker.StateValue.DONE == event.getNewValue()) {
                try {
                    workerDone(worker.get());
                } catch (InterruptedException e) {
                    throw new RuntimeException(e);
                } catch (ExecutionException e) {
                    workerDone(GraphvizResult.makeError(e.toString()));
                }
            }
        });

        pack();
        setLocationRelativeTo(window);
        setVisible(true);
        addWindowListener(this);
    }

    private void stopWorker() {
        if (worker != null) {
            worker.cancel(true);
        }
    }

    private void workerDone(GraphvizResult result) {
        if (result.hasImage()) {
            getContentPane().removeAll();
            PanZoomImageView pziv = new PanZoomImageView(result.getImage(), 800, 600);
            pziv.setPreferredSize(new Dimension(800, 600));
            getContentPane().add(pziv, BorderLayout.CENTER);
        } else if (result.hasError()) {
            JLabel label = new JLabel(result.getError());
            label.setBorder(new EmptyBorder(0, 10, 10, 10));
            getContentPane().add(label, BorderLayout.SOUTH);
        } else {
            JLabel label = new JLabel("Unknown error occurred when executing dot.");
            label.setBorder(new EmptyBorder(0, 10, 10, 10));
            getContentPane().add(label, BorderLayout.SOUTH);
        }
        pack();
        setLocationRelativeTo(window);
    }

    @Override
    public void windowClosing(WindowEvent e) {
        stopWorker();
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
