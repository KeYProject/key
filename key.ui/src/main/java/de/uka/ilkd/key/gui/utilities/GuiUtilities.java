/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.Point;
import java.awt.Toolkit;
import java.awt.datatransfer.StringSelection;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.pp.PosInSequent;

public final class GuiUtilities {

    private GuiUtilities() {
        throw new Error("Do not instantiate");
    }

    /// Copies the content in the bounds of `pos` in the `view` as plain text
    /// into the system clipboard. It translates the nbsp into breakable spaces.
    public static void copyHighlightToClipboard(SequentView view, PosInSequent pos) {
        // Replace nbsp; from html with normal spaces
        String s = view.getHighlightedText(pos).replace('\u00A0', ' ');
        // now CLIPBOARD
        StringSelection ss = new StringSelection(s);
        Toolkit toolkit = Toolkit.getDefaultToolkit();
        toolkit.getSystemClipboard().setContents(ss, ss);
    }


    /**
     * Center a component on the screen.
     *
     * Preconditions: comp.getSize() as on screen.
     *
     * @param comp the component to be centered relative to the screen. It must already have its
     *        final size set.
     *
     * @see #setCenter(Component, Component)
     */
    public static void setCenter(Component comp) {
        Dimension screenSize = comp.getToolkit().getScreenSize();
        Dimension frameSize = comp.getSize();
        if (frameSize.height > screenSize.height) {
            frameSize.height = screenSize.height;
        }
        if (frameSize.width > screenSize.width) {
            frameSize.width = screenSize.width;
        }
        comp.setLocation((screenSize.width - frameSize.width) / 2,
            (screenSize.height - frameSize.height) / 2);
    }

    /**
     * Center a component within a parental component.
     *
     * @param comp the component to be centered.
     * @param parent center relative to what. <code>null</code> to center relative to screen.
     * @see #setCenter(Component)
     */
    public static void setCenter(Component comp, Component parent) {
        if (parent == null) {
            setCenter(comp);
            return;
        }
        Dimension dlgSize = comp.getPreferredSize();
        Dimension frmSize = parent.getSize();
        Point loc = parent.getLocation();
        if (dlgSize.width < frmSize.width && dlgSize.height < frmSize.height) {
            comp.setLocation((frmSize.width - dlgSize.width) / 2 + loc.x,
                (frmSize.height - dlgSize.height) / 2 + loc.y);
        } else {
            setCenter(comp);
        }
    }

    private static final String ESC_COMMAND = "ESC";

    /**
     * Adds a listener to the esc button that clicks the button.
     *
     * @param button the button to click
     */
    public static void attachClickOnEscListener(JButton button) {
        ActionListener escapeListener = event -> {
            if (event.getActionCommand().equals(ESC_COMMAND)) {
                button.doClick();
            }
        };
        button.registerKeyboardAction(escapeListener, ESC_COMMAND,
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0), JComponent.WHEN_IN_FOCUSED_WINDOW);
    }
}
