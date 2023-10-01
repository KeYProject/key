/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.configuration;

import java.awt.*;
import java.awt.event.KeyEvent;
import javax.swing.*;
import javax.swing.text.AttributeSet;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;
import javax.swing.text.PlainDocument;

import de.uka.ilkd.key.settings.ProofIndependentSettings;

/**
 * @deprecated weigl, 2019-05-10: integrated into the
 *             {@link de.uka.ilkd.key.gui.settings.StandardUISettings}
 */
@Deprecated
public class ViewSelector extends JDialog {

    /**
     *
     */
    private static final long serialVersionUID = 5271280688046955444L;
    private JTextField maxTooltipLinesInputField;
    private JCheckBox showWholeTacletCB;
    private JCheckBox showUninstantiatedTacletCB;

    /**
     * creates a new ViewSelector
     *
     * @param parent The parent widget of this ViewSelector
     */
    public ViewSelector(JFrame parent) {
        super(parent, "Maximum line number for tooltips", true);
        layoutViewSelector();
        pack();
        setLocationRelativeTo(parent);
    }


    private void updateButtons() {

    }


    /** lays out the selector */
    protected void layoutViewSelector() {
        // int maxLinesInt = ProofSettings.DEFAULT_SETTINGS.getViewSettings()
        // .getMaxTooltipLines();
        // boolean showWholeTaclet = ProofSettings.DEFAULT_SETTINGS.getViewSettings()
        // .getShowWholeTaclet();
        int maxLinesInt =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getMaxTooltipLines();
        boolean showWholeTaclet =
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().getShowWholeTaclet();
        boolean showUninstantiatedTaclet = ProofIndependentSettings.DEFAULT_INSTANCE
                .getViewSettings().getShowUninstantiatedTaclet();

        getContentPane().setLayout(new BorderLayout());

        JPanel maxLinesPanel = new JPanel();
        maxLinesPanel.setLayout(new BoxLayout(maxLinesPanel, BoxLayout.X_AXIS));
        maxTooltipLinesInputField = new NumberInputField(maxLinesInt, 4);
        maxTooltipLinesInputField.setMaximumSize(new Dimension(40, 30));
        maxLinesPanel.add(new JLabel("<html><font color=\"#000000\">"
            + "Maximum size (line count) of the tooltips of applicable rules"
            + "<br> with schema variable instantiations displayed. "
            + "In case of longer <br>tooltips the instantiation will be "
            + "suppressed. </font></html>"));
        maxLinesPanel.add(maxTooltipLinesInputField);

        JPanel showUninstantiatedTacletPanel = new JPanel();
        showUninstantiatedTacletPanel
                .setLayout(new BoxLayout(showUninstantiatedTacletPanel, BoxLayout.X_AXIS));
        showUninstantiatedTacletCB =
            new JCheckBox("show uninstantiated taclet " + "recommended for unexperienced users",
                showUninstantiatedTaclet);
        showUninstantiatedTacletPanel.add(showUninstantiatedTacletCB);

        JPanel showWholeTacletPanel = new JPanel();
        showWholeTacletPanel.setLayout(new BoxLayout(showWholeTacletPanel, BoxLayout.X_AXIS));
        showWholeTacletCB = new JCheckBox(
            "pretty-print whole Taclet including " + "'name', 'find', 'varCond' and 'heuristics'",
            showWholeTaclet);
        showWholeTacletPanel.add(showWholeTacletCB);

        JPanel tacletOptionsPanel = new JPanel();
        tacletOptionsPanel.setLayout(new GridLayout(2, 1));
        tacletOptionsPanel.add(showWholeTacletPanel);
        tacletOptionsPanel.add(showUninstantiatedTacletPanel);

        JButton okButton = new JButton("OK");
        okButton.setMnemonic(KeyEvent.VK_ENTER);

        okButton.addActionListener(e -> {
            // int maxSteps = Integer.parseInt(maxTooltipLinesInputField.getText());
            // ProofSettings.DEFAULT_SETTINGS.getViewSettings().setMaxTooltipLines(maxSteps);
            // boolean ifind = showWholeTacletCB.isSelected();
            // ProofSettings.DEFAULT_SETTINGS.getViewSettings().setShowWholeTaclet(ifind);
            int maxSteps = Integer.parseInt(maxTooltipLinesInputField.getText());
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setMaxTooltipLines(maxSteps);
            boolean ifind = showWholeTacletCB.isSelected();
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setShowWholeTaclet(ifind);
            boolean uninstTaclet = showUninstantiatedTacletCB.isSelected();
            ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings()
                    .setShowUninstantiatedTaclet(uninstTaclet);
            setVisible(false);
            dispose();
        });
        JButton saveButton = new JButton("Save as Default");

        saveButton.addActionListener(e -> {
            int maxSteps = Integer.parseInt(maxTooltipLinesInputField.getText());
            // ProofSettings dflt=ProofSettings.DEFAULT_SETTINGS;
            ProofIndependentSettings dflt = ProofIndependentSettings.DEFAULT_INSTANCE;
            boolean ifind = showWholeTacletCB.isSelected();
            boolean uninstTaclet = showUninstantiatedTacletCB.isSelected();
            dflt.getViewSettings().setMaxTooltipLines(maxSteps);
            dflt.getViewSettings().setShowWholeTaclet(ifind);
            dflt.getViewSettings().setShowUninstantiatedTaclet(uninstTaclet);
            // temporary solution, stores more than wanted %%%%
            dflt.saveSettings();
            setVisible(false);
            dispose();
        });
        JButton cancelButton = new JButton("Cancel");
        cancelButton.setMnemonic(KeyEvent.VK_ESCAPE);
        cancelButton.addActionListener(e -> {
            setVisible(false);
            dispose();
        });

        JPanel buttonPanel = new JPanel();
        buttonPanel.add(okButton);
        buttonPanel.add(saveButton);
        buttonPanel.add(cancelButton);

        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
        getContentPane().add(maxLinesPanel);
        getContentPane().add(tacletOptionsPanel);
        // getContentPane().add(showWholeTacletPanel);
        getContentPane().add(buttonPanel);

        updateButtons();

    }



    // INNER CLASS TO READ ONLY NUMBERS FOR MAX APPs
    static class NumberDocument extends PlainDocument {

        /**
         *
         */
        private static final long serialVersionUID = -5423315366275141764L;

        public void insertString(int offs, String str, AttributeSet a) throws BadLocationException {
            if (str == null) {
                return;
            }
            char[] upper = str.toCharArray();
            for (char anUpper : upper) {
                if (anUpper < '0' || anUpper > '9') {
                    return;
                }
            }
            super.insertString(offs, new String(upper), a);
        }

    }

    static class NumberInputField extends JTextField {
        /**
         *
         */
        private static final long serialVersionUID = 5578481785681533620L;

        public NumberInputField(int number, int cols) {
            super(cols);
            setText(String.valueOf(number));
        }

        protected Document createDefaultModel() {
            return new NumberDocument();
        }
    }



}
