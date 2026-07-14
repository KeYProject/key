/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.soundiness;

import java.awt.*;
import javax.swing.*;
import javax.swing.border.EmptyBorder;

import de.uka.ilkd.key.proof.Proof;

/**
 * Modal dialog displaying a soundiness report as HTML for a proof.
 *
 * @author opencode
 * @since 3.0
 */
public class SoundinessDialog extends JDialog {

    /**
     * Creates a new soundiness dialog for the given proof.
     *
     * @param owner The parent frame
     * @param proof The proof to analyze
     */
    public SoundinessDialog(Frame owner, Proof proof) {
        super(owner, "Soundiness Report: " + proof.name(), true);
        initUI(proof);
    }

    private void initUI(Proof proof) {
        setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        setLayout(new BorderLayout());

        String html = SoundinessAnalyzer.generateHTMLReport(proof);

        JEditorPane htmlPane = new JEditorPane("text/html", html);
        htmlPane.setEditable(false);
        // htmlPane.putClientProperty(JEditorPane.HONOR_DISPLAY_PROPERTIES, Boolean.TRUE);
        // htmlPane.setFont(UIManager.getFont("Label.font"));
        htmlPane.setPreferredSize(new Dimension(850, 600));

        JScrollPane scrollPane = new JScrollPane(htmlPane);
        scrollPane.setBorder(null);
        scrollPane.setWheelScrollingEnabled(true);

        add(scrollPane, BorderLayout.CENTER);

        JPanel buttonPanel = createButtonPanel(html);
        add(buttonPanel, BorderLayout.SOUTH);

        pack();
        setSize(900, 750);
        setLocationRelativeTo(getOwner());
    }

    private JPanel createButtonPanel(String html) {
        JPanel panel = new JPanel();
        panel.setBorder(new EmptyBorder(10, 10, 10, 10));

        JButton copyButton = new JButton("Copy HTML");
        copyButton.addActionListener(e -> {
            Toolkit.getDefaultToolkit().getSystemClipboard()
                    .setContents(new java.awt.datatransfer.StringSelection(html), null);
            JOptionPane.showMessageDialog(this,
                "HTML copied to clipboard", "Copy",
                JOptionPane.INFORMATION_MESSAGE);
        });
        panel.add(copyButton);

        panel.add(Box.createHorizontalStrut(20));

        JButton closeButton = new JButton("Close");
        closeButton.addActionListener(e -> dispose());
        getRootPane().setDefaultButton(closeButton);
        panel.add(closeButton);

        return panel;
    }
}
