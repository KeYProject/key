package de.uka.ilkd.key.gui.smt;

import java.awt.BorderLayout;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JDialog;
import javax.swing.JPanel;

@SuppressWarnings("serial")
public class TGOptionsDialog extends JDialog {
	
	private static boolean junit, duplicate;
	
	private JCheckBox junitCheckBox,duplicateCheckBox;
	private JButton okButton;
	private JPanel optionsPanel, buttonsPanel;
	
	
	
	
	
	public TGOptionsDialog() {
		super();
		junit = false;
		duplicate = true;
		init();
		
	}

	public static boolean isJunit() {
		return junit;
	}

	public static boolean removeDuplicates() {
		return duplicate;
	}







	private void init(){
		
		junitCheckBox = new JCheckBox(new AbstractAction("JUnit") {
			
			@Override
			public void actionPerformed(ActionEvent e) {
				junit = junitCheckBox.isSelected();
				
			}
		});		
		junitCheckBox.setSelected(junit);
		
		duplicateCheckBox = new JCheckBox(new AbstractAction("Remove duplicates") {
			
			@Override
			public void actionPerformed(ActionEvent e) {
				duplicate = duplicateCheckBox.isSelected();
				
			}
		});		
		duplicateCheckBox.setSelected(duplicate);
		
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
		
		this.setLayout(new BorderLayout());
		this.getContentPane().add(optionsPanel, BorderLayout.CENTER);
		this.getContentPane().add(buttonsPanel, BorderLayout.SOUTH);
		
		this.setTitle("Test Case Generation Options");
		this.pack();
		this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
		this.setModal(true);
		this.setVisible(true);		
	}

}
