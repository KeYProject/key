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
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.text.NumberFormat;

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.ButtonGroup;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JFormattedTextField;
import javax.swing.JLabel;
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

    /**
     * Version ID
     */
    private static final long serialVersionUID = 5731407140427140088L;
    
    public HeatmapOptionsDialog() {
        
        setTitle("Heatmap Options");
        
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        
        JPanel panel = new JPanel();
        panel.setLayout(new GridBagLayout());
        GridBagConstraints c = new GridBagConstraints();
        c.insets = new Insets(10, 5, 10, 5);
        c.ipadx = 0;
        c.ipady = 0;
        
        final int numButtons = 5;
        JRadioButton[] radioButtons = new JRadioButton[numButtons];
        JPanel[] subPanels = new JPanel[numButtons];
        JPanel[] textPanels = new JPanel[numButtons];
        
        final ButtonGroup group = new ButtonGroup();
        JButton okButton = new JButton("OK");
        JButton cancelButton = new JButton("Cancel");


        final String defaultCommand = "default";
        final String sf_age_command = "sf_age";
        final String sf_newest_command = "sf_newest";
        final String terms_age_command = "terms_age";
        final String terms_newest_command = "terms_newest";
        
        String[] descriptions = new String[numButtons];
        descriptions[0] = "No Heatmaps are shown.";
        descriptions[1] = "All sequent formulas below the specified age are highlighted.";
        descriptions[2] = "The newest sequent formulas are highlighted.";
        descriptions[3] = "All terms below the specified age are highlighted.";
        descriptions[4] = "The newest terms are highlighted.";

        radioButtons[0] = new JRadioButton("No Heatmaps");
        radioButtons[0].setActionCommand(defaultCommand);

        radioButtons[1] = new JRadioButton("Sequent formulas up to age");
        radioButtons[1].setActionCommand(sf_age_command);

        radioButtons[2] = new JRadioButton("Newest sequent formulas");
        radioButtons[2].setActionCommand(sf_newest_command);

        radioButtons[3] = new JRadioButton("Terms up to age");
        radioButtons[3].setActionCommand(terms_age_command);

        radioButtons[4] = new JRadioButton("Newest terms");
        radioButtons[4].setActionCommand(terms_newest_command);
        
        NumberFormat format = NumberFormat.getInstance();
        NumberFormatter formatter = new NumberFormatter(format);
        formatter.setValueClass(Integer.class);
        formatter.setMinimum(1);
        formatter.setMaximum(1000);
        formatter.setAllowsInvalid(true);
        
        JFormattedTextField textField = new JFormattedTextField(formatter);

        textField.setPreferredSize(new Dimension(40, 20));
        textField.setMaximumSize(textField.getPreferredSize());
        textField.addPropertyChangeListener(new PropertyChangeListener() {
            
            @Override
            public void propertyChange(PropertyChangeEvent evt) {
                if (textField.getValue() != null ) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setMaxAgeForHeatmap((int) textField.getValue());
                }
            }
            
        });
        textField.setValue(vs.getMaxAgeForHeatmap());
        textField.setToolTipText("Please enter a value between " + formatter.getMinimum() + " and " + formatter.getMaximum() + ".");
        
        for (int i = 0; i < numButtons; i++) {
            textPanels[i] = new JPanel();
            textPanels[i].add(new JLabel(descriptions[i]));
            group.add(radioButtons[i]);
            subPanels[i] = new JPanel();
            subPanels[i].setLayout(new BorderLayout());
            subPanels[i].add(radioButtons[i], BorderLayout.PAGE_START);
            subPanels[i].add(textPanels[i], BorderLayout.WEST);
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
                ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
                if (command == defaultCommand) {
                    vs.setShowHeatmap(false);
                } else if (command == sf_age_command) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(true);
                    vs.setHeatmapNewest(false);
                } else if (command == sf_newest_command) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(true);
                    vs.setHeatmapNewest(true);
                } else if (command == terms_age_command) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(false);
                    vs.setHeatmapNewest(false);
                } else if (command == terms_newest_command) {
                    vs.setShowHeatmap(true);
                    vs.setHeatmapSF(false);
                    vs.setHeatmapNewest(true);
                }
                dispose();
            }
        });
        
        
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                dispose();
            }
        });
        
        JPanel box  = new JPanel();
        box.setLayout(new BoxLayout(box, BoxLayout.Y_AXIS));
        for (int i = 0; i < numButtons; i++) {
            subPanels[i].setBorder(BorderFactory.createBevelBorder(0));
            box.add(subPanels[i]);
        }

        JPanel tfPanel = new JPanel();
        tfPanel.setLayout(new BoxLayout(tfPanel, BoxLayout.Y_AXIS));
        tfPanel.setAlignmentX(Component.CENTER_ALIGNMENT);
        tfPanel.add(new JLabel("<html><body>Maximum age of highlighted <br>terms or formulas, "
                + "or number of <br> newest terms or formulas</body></html>"));
        JPanel tmp = new JPanel(); tmp.add(textField);
        tfPanel.add(tmp);
        tfPanel.setBorder(BorderFactory.createBevelBorder(0));

        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new BoxLayout(buttonPanel, BoxLayout.X_AXIS));
        buttonPanel.add(okButton);
        buttonPanel.add(new JLabel("                     "));
        buttonPanel.add(cancelButton);
        
        c.gridy = 0;
        panel.add(new JLabel("<html><body>Heatmaps can be used to highlight the most recently <br>"
                + "changed terms or sequent formulas. Below, you can <br> "
                + "specify how many terms should be highlighted.</body></html>"), c);
        c.gridy++;
        panel.add(box, c);
        c.gridy++;
        panel.add(tfPanel, c);
        c.gridy++;
        panel.add(buttonPanel, c);
        
//        panel.setSize(200, 4000);
        
        add(panel);
        getRootPane().setDefaultButton(okButton);
        
        pack();
        setLocationRelativeTo(null);
        setVisible(true);
        setResizable(false);
    }
}
