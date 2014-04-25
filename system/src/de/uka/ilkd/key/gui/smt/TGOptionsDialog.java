package de.uka.ilkd.key.gui.smt;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.WindowConstants;

@SuppressWarnings("serial")
public class TGOptionsDialog extends JDialog {
	private static boolean junit, duplicate;

	public static boolean isJunit() {
		return TGOptionsDialog.junit;
	}

	public static boolean removeDuplicates() {
		return TGOptionsDialog.duplicate;
	}

	private JCheckBox junitCheckBox, duplicateCheckBox;
	private JButton okButton;
	private JPanel optionsPanel, buttonsPanel;

	public TGOptionsDialog() {
		super();
		TGOptionsDialog.junit = false;
		TGOptionsDialog.duplicate = true;
		init();
	}

	private void init() {
		junitCheckBox = new JCheckBox(new AbstractAction("JUnit") {
			@Override
			public void actionPerformed(ActionEvent e) {
				TGOptionsDialog.junit = junitCheckBox.isSelected();
			}
		});
		junitCheckBox.setSelected(TGOptionsDialog.junit);
		duplicateCheckBox = new JCheckBox(new AbstractAction(
		        "Remove duplicates") {
			@Override
			public void actionPerformed(ActionEvent e) {
				TGOptionsDialog.duplicate = duplicateCheckBox.isSelected();
			}
		});
		duplicateCheckBox.setSelected(TGOptionsDialog.duplicate);
		optionsPanel = new JPanel(new FlowLayout());
		optionsPanel.add(junitCheckBox);
		optionsPanel.add(duplicateCheckBox);
		okButton = new JButton(new AbstractAction("OK") {
			@Override
			public void actionPerformed(ActionEvent e) {
				dispose();
			}
		});
		buttonsPanel = new JPanel(new FlowLayout());
		buttonsPanel.add(okButton);
		setLayout(new BorderLayout());
		getContentPane().add(optionsPanel, BorderLayout.CENTER);
		getContentPane().add(buttonsPanel, BorderLayout.SOUTH);
		setTitle("Test Case Generation Options");
		pack();
		setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
		setModal(true);
		setVisible(true);
	}
}
