// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.gui.smt;

import java.awt.Dimension;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.BorderFactory;
import javax.swing.Box;
import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JFileChooser;
import javax.swing.JLabel;
import javax.swing.JPanel;
import javax.swing.JSlider;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.JToggleButton;
import javax.swing.SwingUtilities;
import javax.swing.border.TitledBorder;



class PropertyPanel extends JPanel {

    private static final int MAX_LABEL_LENGTH = 10;
    private static final long serialVersionUID = 1L;
    JLabel propertyLabel = null;
    JTextField valueField = null;
    
    private int getMaxWidth(){
	String s ="";
	for(int i=0; i < MAX_LABEL_LENGTH; i++){
	    s+="W";
	}
	return SwingUtilities.computeStringWidth(this.getFontMetrics(this.getFont()),s);
    }
    

    public PropertyPanel() {

	/*GridBagConstraints gridBagConstraints13 = new GridBagConstraints();
	gridBagConstraints13.fill = GridBagConstraints.BOTH;
	gridBagConstraints13.gridy = 0;
	gridBagConstraints13.weightx = 1.0;
	gridBagConstraints13.anchor = GridBagConstraints.NORTHEAST;
	gridBagConstraints13.weighty = 1.0;
	gridBagConstraints13.gridx = 1;
	
	GridBagConstraints gridBagConstraints12 = new GridBagConstraints();
	gridBagConstraints12.gridx = 0;
	gridBagConstraints12.anchor = GridBagConstraints.WEST;
	gridBagConstraints12.weightx = 0.0;
	gridBagConstraints12.weighty = 1.0;
	gridBagConstraints12.gridy = 0;
	
	gridBagConstraints12.insets = new Insets(0,5,0,0); 
	propertyLabel = new JLabel();
	
	propertyLabel.setText("Property Name");
	
	setLayout(new GridBagLayout());
	setSize(new Dimension(289, 23));
	add(propertyLabel, gridBagConstraints12);
	add(getValueField(), gridBagConstraints13);*/
	propertyLabel = new JLabel();
	setLayout(new BoxLayout(this, BoxLayout.X_AXIS));
	
	add(propertyLabel);
	add(Box.createVerticalGlue());
	add(getValueField());
	

	

    }
    
    public void setLabel(String text){
	propertyLabel.setText(text);
	int width = propertyLabel.getPreferredSize().width;
	width = Math.max(getMaxWidth(),width);
	propertyLabel.setPreferredSize(new Dimension(width,propertyLabel.getPreferredSize().height));

	
    }

    /**
     * This method initializes valueField
     * 
     * @return javax.swing.JTextField
     */
    public JTextField getValueField() {
	if (valueField == null) {
	    valueField = new JTextField();
	}
	return valueField;
    }
}


class InfoPanel extends JPanel {
    private static final long serialVersionUID = 1L;
    JLabel propertyLabel = null;
    JToggleButton toggleButton= null;

    public InfoPanel() {

	GridBagConstraints gridBagConstraints13 = new GridBagConstraints();
	//gridBagConstraints13.fill = GridBagConstraints.BOTH;
	gridBagConstraints13.gridy = 0;
	gridBagConstraints13.weightx = 1.0;
	gridBagConstraints13.anchor = GridBagConstraints.SOUTH;
	gridBagConstraints13.weighty = 1.0;
	gridBagConstraints13.gridx = 0;


	setLayout(new GridBagLayout());
	//setSize(new Dimension(289, 23));

	add(getToogleButton(), gridBagConstraints13);

    }

    /**
     * This method initializes valueField
     * 
     * @return javax.swing.JTextField
     */
    public JToggleButton getToogleButton() {
	if (toggleButton == null) {
	    toggleButton = new JToggleButton();
	   // toggleButton.setIcon(IconFactory.saveFile(20));
	    toggleButton.setText("?");
	    toggleButton.setBorderPainted(false);
	    toggleButton.setBackground(this.getBackground());
	    
	}
	return toggleButton;
    }
    
    public boolean isSelected(){
	return getToogleButton().isSelected();
    }
    
    public void setSelected(boolean b){
	getToogleButton().setSelected(b);
    }
}

class SliderPanel extends JPanel{
    private static final long serialVersionUID = 1L;
    	private JSlider slider = null;
    	public SliderPanel() {
		 GridBagConstraints gridBagConstraints7 = new GridBagConstraints();
		 gridBagConstraints7.fill = GridBagConstraints.BOTH;
		 gridBagConstraints7.gridy = 0;
			gridBagConstraints7.weightx = 1.0;
			gridBagConstraints7.weighty = 1.0;
			gridBagConstraints7.insets = new Insets(5, 0, 5, 0);
			gridBagConstraints7.gridx = 0;
			
			setLayout(new GridBagLayout());
			setSize(new Dimension(397, 68));
			setBorder(BorderFactory.createTitledBorder(null, "Timeout:",
				TitledBorder.DEFAULT_JUSTIFICATION,
				TitledBorder.DEFAULT_POSITION, null, null));
			add(getTimeoutSlider(), gridBagConstraints7);
	
		
	}


	private JSlider getTimeoutSlider() {
		slider = new JSlider();
		
		slider = new JSlider();
		slider.setPaintLabels(true);
		
		return slider;
	}
}


class SaveToFilePanel extends JPanel{
    private static final long serialVersionUID = 1L;
	private JCheckBox saveToFileBox = null;
	private JTextField folderField = null;
	private JButton chooseButton = null;
	private JTextArea saveToFileExplanation = null;
	

	
	
	public SaveToFilePanel() {

	    GridBagConstraints gridBagConstraints3 = new GridBagConstraints();
	    gridBagConstraints3.fill = GridBagConstraints.BOTH;
	    gridBagConstraints3.gridy = 1;
	    gridBagConstraints3.weightx = 1.0;
	    gridBagConstraints3.weighty = 1.0;
	    gridBagConstraints3.gridwidth = 2;
	    gridBagConstraints3.ipady = 34;
	    gridBagConstraints3.anchor = GridBagConstraints.CENTER;
	    gridBagConstraints3.insets = new Insets(5, 0, 2, 0);
	    gridBagConstraints3.gridx = 0;
	    GridBagConstraints gridBagConstraints = new GridBagConstraints();
	    gridBagConstraints.gridx = 1;
	    gridBagConstraints.anchor = GridBagConstraints.NORTHWEST;
	    gridBagConstraints.weightx = 0.1;
	    gridBagConstraints.insets = new Insets(0, 6, 0, 0);
	    gridBagConstraints.gridy = 0;
	    GridBagConstraints gridBagConstraints2 = new GridBagConstraints();
	    gridBagConstraints2.fill = GridBagConstraints.BOTH;
	    gridBagConstraints2.gridy = 0;
	    gridBagConstraints2.weightx = 0.5;
	    gridBagConstraints2.anchor = GridBagConstraints.NORTHWEST;
	    gridBagConstraints2.ipadx = 100;
	    gridBagConstraints2.gridx = 0;
	    GridBagConstraints gridBagConstraints1 = new GridBagConstraints();
	    gridBagConstraints1.gridx = 0;
	    gridBagConstraints1.anchor = GridBagConstraints.NORTHWEST;
	    gridBagConstraints1.fill = GridBagConstraints.HORIZONTAL;
	    gridBagConstraints1.weightx = 1.0;
	    gridBagConstraints1.gridy = 2;

	    setLayout(new GridBagLayout());
	    setBorder(BorderFactory.createTitledBorder(null, "Save translated problem to file:",
		    TitledBorder.DEFAULT_JUSTIFICATION, TitledBorder.DEFAULT_POSITION, null, null));
	    setSize(new Dimension(456, 129));
	    add(getSaveToFileBox(), gridBagConstraints1);
	    add(getFolderField(), gridBagConstraints2);
	    add(getChooseButton(), gridBagConstraints);
	   // add(getSaveToFileExplanation(), gridBagConstraints3);
	    getSaveToFileExplanation().setEditable(false);
	    getSaveToFileExplanation().setBackground(this.getBackground());



	}

	/**
	 * This method initializes saveToFileBox	
	 * 	
	 * @return javax.swing.JCheckBox	
	 */
	public JCheckBox getSaveToFileBox() {
		if (saveToFileBox == null) {
			saveToFileBox = new JCheckBox();
			saveToFileBox.setText("activated");
		}
		return saveToFileBox;
	}

	/**
	 * This method initializes folderField	
	 * 	
	 * @return javax.swing.JTextField	
	 */
	public JTextField getFolderField() {
		if (folderField == null) {
			folderField = new JTextField();
		}
		return folderField;
	}

	/**
	 * This method initializes chooseButton	
	 * 	
	 * @return javax.swing.JButton	
	 */
	public JButton getChooseButton() {
		if (chooseButton == null) {
			chooseButton = new JButton();
			chooseButton.setText("choose folder");
			chooseButton.addActionListener(new ActionListener() {
			    
			    public void actionPerformed(ActionEvent e) {
				JFileChooser chooser = new JFileChooser();
				chooser.setFileSelectionMode(JFileChooser.DIRECTORIES_ONLY);
				if(chooser.showDialog(SaveToFilePanel.this, "Choose folder") 
					== JFileChooser.APPROVE_OPTION){
				    getFolderField().setText(chooser.getSelectedFile().getAbsolutePath()+
					"/%d_%t_%i_%s");
				}
			    }
			});
		}
		return chooseButton;
	}

	/**
	 * This method initializes saveToFileExplanation	
	 * 	
	 * @return javax.swing.JTextArea	
	 */
	public JTextArea getSaveToFileExplanation() {
		if (saveToFileExplanation == null) {
			saveToFileExplanation = new JTextArea();
			saveToFileExplanation.setLineWrap(true);
			saveToFileExplanation.setText("Explanation of this field....");
		}
		return saveToFileExplanation;
	}
}


