package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.text.NumberFormat;

import javax.swing.ButtonGroup;
import javax.swing.JFormattedTextField;
import javax.swing.JMenu;
import javax.swing.JMenuItem;
import javax.swing.JRadioButtonMenuItem;
import javax.swing.text.NumberFormatter;

import de.uka.ilkd.key.gui.actions.HeatmapSettingsAction;
import de.uka.ilkd.key.gui.nodeviews.CurrentGoalView;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings.HeatmapMode;

public class HeatmapUtil {
    
    int sf_age;
    int sf_num;
    int terms_age;
    int terms_num;

    public static void setupHeatmapMenu(JMenu view, CurrentGoalView cgv, MainWindow mw) {
        
        JMenuItem hm = new JMenuItem(new HeatmapSettingsAction(mw));
        hm.setText("Heatmap Options");
        view.add(hm);
        
        // to be deleted maybe
        ButtonGroup group = new ButtonGroup();
        JRadioButtonMenuItem nope = new JRadioButtonMenuItem("No Heatmap");
        group.add(nope);
        nope.setSelected(true);
        JRadioButtonMenuItem ageHeatmap = new JRadioButtonMenuItem("Seq formulas up to age ");
        group.add(ageHeatmap);
        JRadioButtonMenuItem newestHeatmap = new JRadioButtonMenuItem("Newest Sequent formulas");
        group.add(newestHeatmap);
        JRadioButtonMenuItem ageTerms = new JRadioButtonMenuItem("Terms up to age");
        group.add(ageTerms);
        JRadioButtonMenuItem newestTerms = new JRadioButtonMenuItem("Newest Terms");
        group.add(newestTerms);
        
        NumberFormat format = NumberFormat.getInstance();
        NumberFormatter formatter = new NumberFormatter(format);
        formatter.setValueClass(Integer.class);
        formatter.setMinimum(1);
        formatter.setMaximum(1000);
        formatter.setAllowsInvalid(false);
        formatter.setCommitsOnValidEdit(true);
        
        JFormattedTextField max_age = new JFormattedTextField(formatter);
        max_age.setToolTipText("Enter a value bewtween 1 and 1000.");
        max_age.setVisible(false);
        
        class HeatmapActionListener implements ActionListener {
            @Override
            public void actionPerformed(ActionEvent e) {
                JRadioButtonMenuItem item = (JRadioButtonMenuItem) e.getSource();
                if (item == nope) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.NONE);
                    max_age.setValue(5);
                    max_age.setVisible(false);
                } else if (item == ageHeatmap) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.AGE_SF);
                    max_age.setVisible(true);
                } else if (item == newestHeatmap) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.NEWEST_SF);
                    max_age.setVisible(true);
                } else if (item == ageTerms) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.AGE_TERMS);
                    max_age.setVisible(true);
                } else if (item == newestTerms) {
                    ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHeatmapMode(HeatmapMode.NEWEST_TERMS);
                    max_age.setVisible(true);
                }
            }
        }
        
        HeatmapActionListener hal = new HeatmapActionListener();
        nope.addActionListener(hal);
        ageHeatmap.addActionListener(hal);
        newestHeatmap.addActionListener(hal);
        ageTerms.addActionListener(hal);
        newestTerms.addActionListener(hal);
        view.add(nope);    
        view.add(ageHeatmap);    
        view.add(newestHeatmap);    
        view.add(ageTerms);    
        view.add(newestTerms);
        
        max_age.addPropertyChangeListener(new PropertyChangeListener() {
            @Override
            public void propertyChange(PropertyChangeEvent evt) {
                if (max_age.getValue() != null) {
                    cgv.setMax_age_for_heatmap((int) max_age.getValue());
                }
            }
        });
        
        view.add(max_age);
    }
}
