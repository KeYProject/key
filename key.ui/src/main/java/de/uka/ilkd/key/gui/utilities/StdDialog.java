/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.awt.*;
import java.awt.event.KeyEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;


/**
 * A dialog offering three buttons at the lower border: Help (optional), Okay and Cancel. The
 * content of the dialog is passed to the dialog by the constructor of the class. You can access the
 * three buttons (in order to add some action listeners) by: <code>getOkButton()</code>
 * <code>getCancelButton()</code> <code>getHelpButton()</code>
 *
 *
 * If you want to see how the dialog looks like execute the method <code>main</code> at the bottom
 * of this file.
 */
public class StdDialog extends JDialog {

    private static final long serialVersionUID = 1L;
    private JButton helpButton;
    private JButton okButton;
    private JButton cancelButton;
    private boolean okButtonHasBeenPressed = false;
    private boolean cancelButtonHasBeenPressed = false;
    private Box contentBox;

    public StdDialog(String title, int strut, boolean helpButton) {
        this(title, null, strut, helpButton);
    }

    public StdDialog(String title, JComponent content, int strut, boolean helpButton) {
        this.setTitle(title);
        this.setModal(true);
        // content.setMaximumSize(new Dimension(Integer.MAX_VALUE,Integer.MAX_VALUE));
        Box vertBox = Box.createVerticalBox();
        Box horzBox = Box.createHorizontalBox();

        vertBox.add(Box.createVerticalStrut(strut));

        horzBox.add(Box.createHorizontalStrut(strut));
        horzBox.add(getContentBox());
        horzBox.add(Box.createHorizontalGlue());
        horzBox.add(Box.createHorizontalStrut(strut));
        vertBox.add(horzBox);
        vertBox.add(Box.createVerticalStrut(strut));
        horzBox = Box.createHorizontalBox();
        horzBox.add(Box.createHorizontalStrut(strut));
        if (helpButton) {
            horzBox.add(getHelpButton());
            horzBox.add(Box.createHorizontalStrut(strut));
        }
        horzBox.add(Box.createHorizontalGlue());
        horzBox.add(getOkButton());
        horzBox.add(Box.createHorizontalStrut(strut));
        horzBox.add(getCancelButton());
        horzBox.add(Box.createHorizontalStrut(strut));
        vertBox.add(horzBox);

        vertBox.add(Box.createVerticalStrut(strut));
        this.getContentPane().add(vertBox);
        this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        this.addWindowListener(new WindowAdapter() {
            @Override
            public void windowClosing(WindowEvent e) {
                getCancelButton().doClick();
            }
        });
        if (content != null) {
            setContent(content);
        } else {
            this.pack();
        }
        this.setLocationRelativeTo(MainWindow.getInstance());
    }

    public void setContent(JComponent content) {
        getContentBox().removeAll();
        getContentBox().add(content);
        content.setMaximumSize(new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE));
        this.pack();
    }



    public boolean okButtonHasBeenPressed() {
        return okButtonHasBeenPressed;
    }

    public boolean cancelButtonHasBeenPressed() {
        return cancelButtonHasBeenPressed;
    }

    public JButton getHelpButton() {
        if (helpButton == null) {
            helpButton = new JButton("Help");
        }
        return helpButton;
    }

    public JButton getOkButton() {
        if (okButton == null) {
            okButton = new JButton("OK");
            okButton.addActionListener(e -> {
                okButtonHasBeenPressed = true;
                StdDialog.this.dispose();

            });
            okButton.setMnemonic(KeyEvent.VK_O);
        }
        return okButton;
    }

    public JButton getCancelButton() {
        if (cancelButton == null) {
            cancelButton = new JButton("Cancel");
            cancelButton.addActionListener(e -> {
                cancelButtonHasBeenPressed = true;
                StdDialog.this.dispose();
            });
            cancelButton.setMnemonic(KeyEvent.VK_C);
        }
        return cancelButton;
    }

    private Box getContentBox() {
        if (contentBox == null) {
            contentBox = Box.createVerticalBox();
            contentBox.setMaximumSize(new Dimension(Integer.MAX_VALUE, Integer.MAX_VALUE));
        }
        return contentBox;
    }

    public static void main(String[] args) {
        final StdDialog dialog = new StdDialog("Test", new JButton("Test"), 5, true);
        dialog.getOkButton().addActionListener(arg0 -> JOptionPane.showMessageDialog(dialog, "OK"));
        dialog.setModal(true);
        dialog.setVisible(true);
    }


}
