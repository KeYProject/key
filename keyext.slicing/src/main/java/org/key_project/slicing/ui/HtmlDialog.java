/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.awt.*;
import java.awt.event.KeyEvent;
import java.util.function.Consumer;
import javax.swing.*;
import javax.swing.event.HyperlinkEvent;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Dialog that displays an HTML document.
 *
 * @author Arne Keller
 */
public class HtmlDialog extends JDialog {

    /**
     * Construct and show a new dialog for the provided HTML.
     *
     * @param window parent window
     * @param title title of the new dialog
     * @param html HTML to show
     * @param linkPressedCallback if the user clicks on a link, this callback receives the URL
     */
    public HtmlDialog(Window window, String title, String html,
            Consumer<String> linkPressedCallback) {
        super(window, title);

        setLayout(new BorderLayout());

        JEditorPane htmlContent = new JEditorPane("text/html", html);
        htmlContent.setEditable(false);
        htmlContent.setBorder(BorderFactory.createEmptyBorder());
        htmlContent.setCaretPosition(0);
        htmlContent.setBackground(MainWindow.getInstance().getBackground());
        htmlContent.setSize(new Dimension(10, 360));
        htmlContent.setPreferredSize(
            new Dimension(Math.min(800, htmlContent.getPreferredSize().width + 15), 360));
        if (linkPressedCallback != null) {
            htmlContent.addHyperlinkListener(event -> {
                if (event.getEventType() == HyperlinkEvent.EventType.ACTIVATED) {
                    // pass the URL along
                    linkPressedCallback.accept(event.getDescription());
                }
            });
        }

        JScrollPane scrollPane = new JScrollPane(htmlContent);
        scrollPane.setBorder(BorderFactory.createEmptyBorder());

        JPanel buttonPane = new JPanel();

        JButton okButton = new JButton("Close");
        okButton.addActionListener(event -> dispose());
        KeyStroke stroke = KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0);
        rootPane.registerKeyboardAction(e -> dispose(), stroke, JComponent.WHEN_IN_FOCUSED_WINDOW);

        buttonPane.add(okButton);

        getRootPane().setDefaultButton(okButton);

        setLayout(new BorderLayout());
        add(scrollPane, BorderLayout.CENTER);
        add(buttonPane, BorderLayout.PAGE_END);

        int w = 50
                + Math.max(
                    scrollPane.getPreferredSize().width,
                    buttonPane.getPreferredSize().width);
        int h = scrollPane.getPreferredSize().height
                + buttonPane.getPreferredSize().height
                + 100;
        setSize(w, h);
        setLocationRelativeTo(window);

        setVisible(true);
    }
}
