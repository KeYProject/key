/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import javax.swing.*;
import javax.swing.border.BevelBorder;

import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

/**
 * Status line of the KeY MainWindow.
 * <p>
 * The status line hold a lblStatusText and a progress panel.
 * <p>
 * You add additional components by using the extension points
 * {@link de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.StatusLine}
 *
 * <p>
 * <ul>
 * <li>08.04.2019, weigl: Clean up, add extension point</li>
 * </ul>
 * </p>
 *
 * @see MainWindow
 * @see de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.StatusLine
 */
class MainStatusLine extends JPanel {
    private static final long serialVersionUID = 2278249652314818379L;
    private final JLabel lblStatusText = new JLabel();
    private final JProgressBar progressBar = new JProgressBar();

    MainStatusLine(String initialText, Font font) {
        setLayout(new BoxLayout(this, BoxLayout.X_AXIS));

        setBorder(new BevelBorder(BevelBorder.LOWERED));
        setBackground(Color.gray);
        setFont(font);
        setOpaque(false);

        lblStatusText.setText(initialText);
        lblStatusText.setIcon(IconFactory.keyLogo(35, 20));
        lblStatusText.setBorder(BorderFactory.createCompoundBorder(lblStatusText.getBorder(),
            BorderFactory.createEmptyBorder(0, 10, 0, 0)));

        // add(Box.createHorizontalGlue());
        add(lblStatusText);
        add(Box.createHorizontalStrut(50));

        progressBar.setValue(0);
        progressBar.setStringPainted(true);
        progressBar.setMaximumSize(new Dimension(100, Short.MAX_VALUE));
        progressBar.setEnabled(true);
        progressBar.setVisible(false);
        add(progressBar);

        add(Box.createHorizontalGlue());
        JToolBar bar = new JToolBar();
        bar.setFloatable(false);
        bar.setRollover(false);
        bar.setBorderPainted(false);
        add(bar);
        KeYGuiExtensionFacade.getStatusLineComponents().forEach(bar::add);
    }

    /*
     * The following methods should only be called from the event dispatching thread
     */

    /**
     * Make the status line display a standard message
     */
    public void reset() {
        setProgressPanelVisible(false);
        lblStatusText.setText("");
    }

    /**
     * Set the range of values the progress bar can display (see <code>setMaximum</code> of
     * <code>ProgressBar</code>)
     */
    public void setProgressBarMaximum(int value) {
        progressBar.setMaximum(value);
    }

    /**
     * Set the value the progress bar currently displays
     */
    public void setProgress(final int value) {
        SwingUtilities.invokeLater(() -> progressBar.setValue(value));
    }

    /**
     * Set the visibility of the progress bar and the abort button
     */
    public void setProgressPanelVisible(boolean visible) {
        progressBar.setVisible(visible);
        if (visible) {
            setProgress(0);

            /*
             * To avoid later resizing of the status line, add an // invisible element with the same
             * height as the abort button if (!phantomBoxAdded) { phantomBoxAdded = true;
             * ComponentListener phantomAdder = new ComponentAdapter() {
             *
             * @Override public void componentResized(ComponentEvent e) {
             * progressPanel.removeComponentListener(this); Dimension s = progressPanel.getSize(); s
             * = new Dimension(0, (int) s.getHeight()); add(Box.createRigidArea(s)); } };
             * progressPanel.addComponentListener(phantomAdder); }
             */
        }
    }

    /**
     * Make the status line display the given string, don't modify anything else
     */
    public void setStatusText(String s) {
        lblStatusText.setText(s);
    }
}
