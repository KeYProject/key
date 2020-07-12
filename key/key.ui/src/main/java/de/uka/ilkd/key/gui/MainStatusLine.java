// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.gui.extension.impl.KeYGuiExtensionFacade;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import javax.swing.*;
import javax.swing.border.BevelBorder;
import java.awt.*;

/**
 * Status line of the KeY MainWindow.
 * <p>
 * The status line hold a lblStatusText and a progress panel.
 * <p>
 * You add additional components by using the extension points {@link de.uka.ilkd.key.gui.extension.api.KeYGuiExtension.StatusLine}
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
    //private boolean phantomBoxAdded = false;

    MainStatusLine(String initialText, Font font) {
        setLayout(new BoxLayout(this, BoxLayout.X_AXIS));

        setBorder(new BevelBorder(BevelBorder.LOWERED));
        setBackground(Color.gray);
        setFont(font);
        setOpaque(false);

        lblStatusText.setText(initialText);
        lblStatusText.setIcon(IconFactory.keyLogo(35, 20));

        //add(Box.createHorizontalGlue());
        add(lblStatusText);
        add(Box.createHorizontalStrut(50));

        progressBar.setValue(0);
        progressBar.setStringPainted(true);
        progressBar.setMaximumSize(new Dimension(100, Short.MAX_VALUE));
        progressBar.setEnabled(true);
        progressBar.setVisible(false);
        add(progressBar);

        add(Box.createHorizontalGlue());
        KeYGuiExtensionFacade.getStatusLineComponents().forEach(this::add);
    }

    /*
     * The following methods should only be called from the event
     * dispatching thread
     */

    /**
     * Make the status line display a standard message
     */
    public void reset() {
        setProgressPanelVisible(false);
    }

    /**
     * Set the range of values the progress bar can display (see
     * <code>setMaximum</code> of <code>ProgressBar</code>)
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

            /* To avoid later resizing of the status line, add an
            // invisible element with the same height as the abort button
            if (!phantomBoxAdded) {
                phantomBoxAdded = true;
                ComponentListener phantomAdder = new ComponentAdapter() {
                    @Override
                    public void componentResized(ComponentEvent e) {
                        progressPanel.removeComponentListener(this);
                        Dimension s = progressPanel.getSize();
                        s = new Dimension(0, (int) s.getHeight());
                        add(Box.createRigidArea(s));
                    }
                };
                progressPanel.addComponentListener(phantomAdder);
            }*/
        }
    }

    /**
     * Make the status line display the given string, don't modify
     * anything else
     */
    public void setStatusText(String s) {
        lblStatusText.setText(s);
    }
}