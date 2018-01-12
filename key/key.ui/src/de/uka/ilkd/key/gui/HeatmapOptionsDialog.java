package de.uka.ilkd.key.gui;

import java.awt.BorderLayout;
import java.awt.Dimension;
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

public class HeatmapOptionsDialog extends JDialog {

    /**
     * Version ID
     */
    private static final long serialVersionUID = 5731407140427140088L;
    
    //TODO nur noch ein feld; werte übernehmen; anpassung verhalten in curgoalview; schön machen

    public HeatmapOptionsDialog() {
        
        ViewSettings vs = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings();
        
        JPanel panel = new JPanel(new BorderLayout());
        
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
        
        String[] descriptions = new String[numButtons];
        descriptions[0] = "No Heatmaps are shown.";
        descriptions[1] = "All sequent formulas below the spefied age are highlighted.";
        descriptions[2] = "The newest sequent formulas are highlighted.";
        descriptions[3] = "All terms below the spefied age are highlighted.";
        descriptions[4] = "The newest terms are highlighted.";

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
        
        JFormattedTextField textField = new JFormattedTextField(formatter);

        textField.setPreferredSize(new Dimension(40, 20));
        textField.addPropertyChangeListener(new PropertyChangeListener() {
            
            @Override
            public void propertyChange(PropertyChangeEvent evt) {
                if (textField.getValue() != null ) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setMaxAgeForHeatmap((int) textField.getValue());
                }
            }
            
        });
        
        textField.setValue(vs.getMaxAgeForHeatmap());
        
        for (int i = 0; i < numButtons; i++) {
            textPanels[i] = new JPanel();
            textPanels[i].add(new JLabel(descriptions[i]));
            group.add(radioButtons[i]);
            subPanels[i] = new JPanel();
            subPanels[i].setLayout(new BoxLayout(subPanels[i], BoxLayout.Y_AXIS));
            subPanels[i].add(radioButtons[i]);
            subPanels[i].add(textPanels[i]);
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

        okButton = new JButton("OK");
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent e) {
                if (group.getSelection() == null) {
                    dispose();
                    return;
                }
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
        JPanel box  = new JPanel();
        box.setLayout(new BoxLayout(box, BoxLayout.Y_AXIS));
        for (int i = 0; i < numButtons; i++) {
            subPanels[i].setBorder(BorderFactory.createBevelBorder(0));
            box.add(subPanels[i]);
            
        }
//        panel.setBorder(BorderFactory.createEmptyBorder(30, 50, 100, 20));
        panel.add(box, BorderLayout.PAGE_START);
        panel.add(textField);
        panel.add(okButton, BorderLayout.PAGE_END);
        
        add(panel);
        pack();
        setLocationRelativeTo(null);
        setVisible(true);
        setResizable(false);
    }
}
