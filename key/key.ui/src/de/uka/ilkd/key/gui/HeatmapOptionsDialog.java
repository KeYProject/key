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

import java.awt.BorderLayout;
import java.awt.Component;
import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.text.NumberFormat;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFormattedTextField;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.text.NumberFormatter;

import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * This Dialog contains options for highlighting sequent formulas 
 * or terms according to their age, i.e., when they were first introduced
 * into the proof. It is possible to highlight all sf/terms up to a 
 * specified age, or to highlight the x newest sf/terms, x being 
 * specified by the user.
 * 
 * @author jschiffl
 *
 */

public class HeatmapOptionsDialog extends JDialog {
    //TODO zweiteilung erklären.
    /**
     * Version ID
     */
    private static final long serialVersionUID = 5731407140427140088L;
    
    private static final int MIN_AGE = 1;
    
    private static final int MAX_AGE = 1000;

    private static final String INTRO_LABEL = "<html><body>Heatmaps can be used to highlight the most recent <br>"
            + "changes in the sequent. You can choose to highlight <br> "
            + "entire sequent formulas or subterms.  Highlighting can either <br>"
            + "be done on the newest expressions, or on all expressions <br>"
            + "that have changed whithin the last <i> k </i> steps of the proof. <br>"
            + "Newer expressions will have a stronger highlight. </body></html>";

    private static final String TEXTFIELD_LABEL = "<html><body>Maximum age of highlighted <br>terms or formulas, "
            + "or number of <br> newest terms or formulas</body></html>";

    private static final String TOOLTIP_TEXT = "Please enter a number between " + MIN_AGE + " and " + MAX_AGE + ".";
    
    public static final String[] COMMANDS = {"default", "sf_age", "sf_newest", "terms_age", "terms_newest"};
    
    public static final String[] BUTTON_DESC = {"No Heatmaps", "Sequent formulas up to age", 
            "Newest sequent formulas", "Terms up to age", "Newest terms"};
    
    public static final String[] DESCRIPTIONS = {"No Heatmaps are shown.",
            "<html><body>All sequent formulas that have changed in the last <i> k </i> steps are highlighted.</body></html>",
            "<html><body>The <i> k </i> newest sequent formulas are highlighted.</body></html>",
            "<html><body>All terms that have changed in the last <i> k </i> steps are highlighted.</body></html>",
            "<html><body>The <i> k </i> newest terms are highlighted.</body></html>"};
    
    private static final String INPUT_ERROR_MESSAGE = "Please enter a number bwetween 1 and 1000";
    
    public HeatmapOptionsDialog() {
        
        setTitle("Heatmap Options");
        
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        
        JPanel panel = new JPanel();
        panel.setLayout(new GridBagLayout());
        GridBagConstraints c = new GridBagConstraints();
        c.insets = new Insets(10, 5, 10, 5);
        c.ipadx = 0;
        c.ipady = 0;
        
        final int numRadioButtons = 5;
        JRadioButton[] radioButtons = new JRadioButton[numRadioButtons];
        
        final ButtonGroup group = new ButtonGroup();
        JButton okButton = new JButton("OK");
        JButton cancelButton = new JButton("Cancel");
        
        NumberFormat format = NumberFormat.getInstance();
        NumberFormatter formatter = new NumberFormatter(format);
        formatter.setValueClass(Integer.class);
        formatter.setMinimum(MIN_AGE);
        formatter.setMaximum(MAX_AGE);
        formatter.setAllowsInvalid(true);
        
        JFormattedTextField textField = new JFormattedTextField(formatter);

        textField.setPreferredSize(new Dimension(40, 20));
        textField.setMaximumSize(textField.getPreferredSize());
        textField.setFocusLostBehavior(JFormattedTextField.COMMIT);
        textField.setValue(vs.getMaxAgeForHeatmap());
        textField.setToolTipText(TOOLTIP_TEXT);
        
        for (int i = 0; i < numRadioButtons; i++) {
            radioButtons[i] = new JRadioButton(BUTTON_DESC[i]);
            radioButtons[i].setActionCommand(COMMANDS[i]);
            group.add(radioButtons[i]);
        }
        
        if (vs.isShowHeatmap()) {
            if (vs.isHeatmapSF()) {
                if (vs.isHeatmapNewest()) {
                    radioButtons[2].setSelected(true);
                } else {
                    radioButtons[1].setSelected(true);
                }
            } else {
                if (vs.isHeatmapNewest()) {
                    radioButtons[4].setSelected(true);
                } else {
                    radioButtons[3].setSelected(true);
                }
            } 
        } else {
            radioButtons[0].setSelected(true);
        }

        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                String command = group.getSelection().getActionCommand();
                if (command == COMMANDS[0]) {
                    vs.setShowHeatmap(false);
                    dispose();
                } else if (command == COMMANDS[1]) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(true);
                    vs.setHeatmapNewest(false);
                } else if (command == COMMANDS[2]) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(true);
                    vs.setHeatmapNewest(true);
                } else if (command == COMMANDS[3]) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(false);
                    vs.setHeatmapNewest(false);
                } else if (command == COMMANDS[4]) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(false);
                    vs.setHeatmapNewest(true);
                }
                if (textField.getValue() != null ) {
                    if (textField.isEditValid()) {
                        vs.setMaxAgeForHeatmap((int) textField.getValue());
                        dispose();
                    } else {
                        JOptionPane.showMessageDialog(panel,
                                INPUT_ERROR_MESSAGE,
                                "Invalid Input",
                                JOptionPane.ERROR_MESSAGE);
                    }
                }
            }
        });
        
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                dispose();
            }
        });
        
        JPanel radioBoxes  = new JPanel();
        radioBoxes.setLayout(new BoxLayout(radioBoxes, BoxLayout.Y_AXIS));
        for (int i = 0; i < numRadioButtons; i++) {
            JPanel p = new JPanel();
            p.setLayout(new BorderLayout());
            p.add(radioButtons[i], BorderLayout.PAGE_START);
            p.add(new JLabel(DESCRIPTIONS[i]));
            p.setBorder(BorderFactory.createBevelBorder(0));
            radioBoxes.add(p);
        }

        JPanel tfPanel = new JPanel();
        tfPanel.setLayout(new BorderLayout());
        tfPanel.add(new JLabel(TEXTFIELD_LABEL), BorderLayout.NORTH);
        JPanel tmp = new JPanel(); tmp.add(new JLabel("k = ")); tmp.add(textField);
        tfPanel.add(tmp, BorderLayout.CENTER);
        tfPanel.setBorder(BorderFactory.createBevelBorder(0));

        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
        buttonPanel.add(okButton);
        buttonPanel.add(new JLabel("                   "));
        buttonPanel.add(cancelButton);
        
        c.gridy = 0;
        panel.add(new JLabel(INTRO_LABEL), c);
        c.gridy++;
        panel.add(radioBoxes, c);
        c.gridy++;
        panel.add(tfPanel, c);
        c.gridy++;
        panel.add(buttonPanel, c);
        
        add(panel);
        getRootPane().setDefaultButton(okButton);
        
        pack();
        setLocationRelativeTo(null);
        setVisible(true);
        setResizable(false);
    }
}
