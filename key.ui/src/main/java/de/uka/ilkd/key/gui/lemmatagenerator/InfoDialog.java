/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.lemmatagenerator;

import java.awt.Component;
import javax.swing.Box;
import javax.swing.JCheckBox;
import javax.swing.JOptionPane;
import javax.swing.JTextPane;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class InfoDialog {
    private @Nullable JTextPane infoText;
    private @Nullable JCheckBox showAgainBox;

    private @Nullable Box box;

    public boolean showDialog(String text, Component parent) {
        getInfoText().setText(text);
        Object[] options = { "Cancel", "Continue" };
        int n = JOptionPane.showOptionDialog(parent, getBox(), "Warning",
            JOptionPane.YES_NO_CANCEL_OPTION, JOptionPane.WARNING_MESSAGE, null, options,
            options[0]);
        return n == 1;
    }

    public boolean showThisDialogNextTime() {
        JCheckBox box = showAgainBox;
        if (box == null) {
            // only asked after the dialog was actually shown
            throw new NullPointerException("No show-again checkbox available.");
        }
        return !box.isSelected();
    }

    private Box getBox() {
        Box result = box;
        if (result == null) {
            Box created = Box.createVerticalBox();
            if (created == null) {
                // a newly created vertical box is never null
                throw new NullPointerException("No vertical box available.");
            }
            created.add(getInfoText());
            created.add(getShowAgainBox());
            JTextPane text = getInfoText();
            text.setBackground(created.getBackground());
            box = created;
            result = created;
        }
        return result;
    }

    private JTextPane getInfoText() {
        if (infoText == null) {
            infoText = new JTextPane();
            infoText.setEditable(false);
        }
        return infoText;
    }

    private JCheckBox getShowAgainBox() {
        if (showAgainBox == null) {
            showAgainBox = new JCheckBox("Don't show this dialog again.");

        }
        return showAgainBox;
    }

}
