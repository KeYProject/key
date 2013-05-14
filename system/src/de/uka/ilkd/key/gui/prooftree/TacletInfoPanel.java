/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.prooftree;

import java.awt.BorderLayout;
import javax.swing.JCheckBox;
import javax.swing.JPanel;
import javax.swing.JTextArea;
import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;

/**
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TacletInfoPanel extends JPanel {

    private final JTextArea tacletInfo = new JTextArea();
    private final JCheckBox tacletInfoToggle = new JCheckBox("Show taclet info (Inner Nodes only)");

    public void setText(String s) {
        tacletInfo.setText(s);
        tacletInfo.setVisible(
                tacletInfoToggle.isSelected());
    }

    TacletInfoPanel() {

        setLayout(new BorderLayout());
        add(tacletInfoToggle, BorderLayout.CENTER);
        add(tacletInfo, BorderLayout.SOUTH);

        tacletInfoToggle.addChangeListener(new ChangeListener() {
            public void stateChanged(ChangeEvent e) {
                tacletInfo.setVisible(
                        tacletInfoToggle.isSelected());
            }
        });
        tacletInfo.setVisible(false);
    }
}
