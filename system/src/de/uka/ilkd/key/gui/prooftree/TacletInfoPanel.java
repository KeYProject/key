/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.prooftree;

import java.awt.BorderLayout;
import javax.swing.JCheckBox;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
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
    private final JScrollPane tacletInfoScrollPane = new JScrollPane(tacletInfo);

    public void setText(String s) {
        tacletInfo.setText(s);
        tacletInfoScrollPane.setVisible(
                tacletInfoToggle.isSelected());
    }

    TacletInfoPanel() {
        
        setLayout(new BorderLayout());
        add(tacletInfoToggle, BorderLayout.NORTH);
        add(tacletInfoScrollPane, BorderLayout.CENTER);

        tacletInfoToggle.addChangeListener(new ChangeListener() {
            public void stateChanged(ChangeEvent e) {
                tacletInfoScrollPane.setVisible(
                        tacletInfoToggle.isSelected());
            }
        });
    }
}
