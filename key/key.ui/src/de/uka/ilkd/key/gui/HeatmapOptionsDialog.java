package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Color;
import java.awt.Dimension;
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
import javax.swing.JPanel;
import javax.swing.JRadioButton;
import javax.swing.JTextField;
import javax.swing.text.NumberFormatter;

import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings.HeatmapMode;

public class HeatmapOptionsDialog extends JDialog {

    /**
     * Version ID
     */
    private static final long serialVersionUID = 5731407140427140088L;
    
    //TODO Textfeld-Action listener, ok button nimmt textfeldwerte und enter-taste, doku im programm, doku im code

    public HeatmapOptionsDialog() {
        JPanel panel = new JPanel();
        
        final int numButtons = 5;
        JRadioButton[] radioButtons = new JRadioButton[numButtons];
        JPanel[] subPanels = new JPanel[numButtons];
        JPanel[] textPanels = new JPanel[numButtons];
        
        final ButtonGroup group = new ButtonGroup();
        JButton okButton = null;

        final String defaultCommand = "default";
        final String sf_age_command = "sf_age";
        final String sf_newest_command = "sf_newest";
        final String terms_age_command = "terms_age";
        final String terms_newest_command = "terms_newest";

        radioButtons[0] = new JRadioButton("No Heatmap");
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
        
        int numOfTextFields = 4;
        JFormattedTextField[] textFields = new JFormattedTextField[numOfTextFields];

        for (int i = 0; i < numOfTextFields; i++) {
            textFields[i] = new JFormattedTextField(formatter);
            textFields[i].setPreferredSize(new Dimension(40, 20));
        }
        
        for (int i = 0; i < numButtons; i++) {
            textPanels[i] = new JPanel();
        }
        textPanels[0].add(new JLabel("No Heatmaps are shown."));
        textPanels[1].add(new JLabel("Sequent formulas up to age "));
        textPanels[1].add(textFields[0]);
        textPanels[1].add(new JLabel(" will be highlighted according to their age."));
        textPanels[2].add(new JLabel("The "));
        textPanels[2].add(textFields[1]);
        textPanels[2].add(new JLabel(" newest sequent formulas will be highlighted."));
        textPanels[3].add(new JLabel("Terms formulas up to age "));
        textPanels[3].add(textFields[2]);
        textPanels[3].add(new JLabel(" will be highlighted according to their age."));
        textPanels[4].add(new JLabel("The "));
        textPanels[4].add(textFields[3]);
        textPanels[4].add(new JLabel(" newest terms will be highlighted."));
        
        for (int i = 0; i < numButtons; i++) {
            group.add(radioButtons[i]);
            subPanels[i] = new JPanel();
            subPanels[i].setLayout(new BoxLayout(subPanels[i], BoxLayout.Y_AXIS));
            subPanels[i].add(radioButtons[i]);
            subPanels[i].add(textPanels[i]);
        }

        okButton = new JButton("OK");
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                String command = group.getSelection().getActionCommand();

                if (command == defaultCommand) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.NONE);
                } else if (command == sf_age_command) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.AGE_SF);
                } else if (command == sf_newest_command) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.NEWEST_SF);
                } else if (command == terms_age_command) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.AGE_TERMS);
                } else if (command == terms_newest_command) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.NEWEST_TERMS);
                }
            }
        });
        JPanel box  = new JPanel();
        box.setLayout(new BoxLayout(box, BoxLayout.Y_AXIS));
        for (int i = 0; i < numButtons; i++) {
            subPanels[i].setBorder(BorderFactory.createLineBorder(Color.BLACK));
            box.add(subPanels[i]);
            
        }
//        panel.setBorder(BorderFactory.createEmptyBorder(30, 50, 100, 20));
        panel.add(box, BorderLayout.PAGE_START);
        panel.add(okButton, BorderLayout.PAGE_END);
        
        add(panel);
        pack();
        setLocationRelativeTo(null);
        setVisible(true);
        setResizable(false);
    }
}
