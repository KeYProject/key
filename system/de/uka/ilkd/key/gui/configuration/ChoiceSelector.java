// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.configuration;

import java.awt.Dimension;
import java.awt.BorderLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.HashMap;
import java.util.Set;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;



public class ChoiceSelector extends JDialog {

    private ChoiceSettings settings;
    private HashMap category2DefaultChoice;
    private HashMap category2Choices;
    private boolean changed=false;


    /** the JList with the categories of choices*/
    private JList catList;
    /** the JList with the choices for one category */
    private JList choiceList;

    /** creates a new ChoiceSelector, using the <code>ChoiceSettings</code>
     * from <code>settings</code> */
    public ChoiceSelector(ChoiceSettings settings) {  
	super(new JFrame(), "Select Default Choices", true);
       	this.settings = settings;
	category2DefaultChoice = settings.getDefaultChoices();
	if(category2DefaultChoice.isEmpty()){
	    JOptionPane.showConfirmDialog
		(ChoiceSelector.this,
		 "There are no Taclet Options available as the rule-files "+
		 "have not been parsed yet!",
		 "No Options available", 
		 JOptionPane.DEFAULT_OPTION);
	    dispose();
	}else{
	    category2Choices = settings.getChoices();
	    layoutChoiceSelector();
	    pack();
	    setLocation(70, 70);
	    setVisible(true);
	}
    }

    /** creates a new ChoiceSelector */
    public ChoiceSelector(){
	this(ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
    }

    /** layout */
    protected void layoutChoiceSelector() {
	Object[] cats = category2DefaultChoice.keySet().toArray();
        java.util.Arrays.sort(cats);
	catList = new JList(cats);
	catList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	catList.setSelectedIndex(0);
	catList.addListSelectionListener(new ListSelectionListener() {
	    public void valueChanged(ListSelectionEvent e) {
		setChoiceList();				
	    }});
	choiceList = new JList(((Set) category2Choices.
				get(cats[0])).toArray());
	choiceList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	choiceList.setSelectedValue(category2DefaultChoice.get(cats[0]),true);
	choiceList.addListSelectionListener(new ListSelectionListener() {
	    public void valueChanged(ListSelectionEvent e) {
		setDefaultChoice((String) choiceList.getSelectedValue());
	    }});

	JScrollPane catListScroll = new
	    JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
			JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	catListScroll.getViewport().setView(catList);
	catListScroll.setBorder(new TitledBorder("Category"));

	JScrollPane choiceScrollPane = new 	    
	    JScrollPane(JScrollPane.VERTICAL_SCROLLBAR_AS_NEEDED, 
			JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED);
	choiceScrollPane.getViewport().setView(choiceList);
	choiceScrollPane.setBorder(new TitledBorder("Default Option"));

	JButton ok = new JButton("OK");
	ok.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if(changed){
			int res = JOptionPane.showOptionDialog
			    (ChoiceSelector.this,
			     "Your changes will become effective when "+
			     "the next problem is loaded.\n", 
			     "Taclet Option Settings", 
			     JOptionPane.DEFAULT_OPTION,
			     JOptionPane.QUESTION_MESSAGE, null,
			     new Object[]{"OK", "Cancel"}, "OK");
			if (res==0){
			    settings.setDefaultChoices(
				category2DefaultChoice);
			}
		    }
		    setVisible(false);
		    dispose();
		}
	    });
	JButton cancel = new JButton("Cancel");
	cancel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    setVisible(false);
		    dispose();
		}
	    });
 	JPanel buttonPanel = new JPanel();
 	buttonPanel.add(ok);
 	buttonPanel.add(cancel);


	Dimension paneDim = new Dimension(300, 300);
	choiceScrollPane.setPreferredSize(paneDim);
	choiceScrollPane.setMinimumSize(paneDim);
	paneDim = new Dimension(200, 300);
	catListScroll.setPreferredSize(paneDim);
        catListScroll.setMinimumSize(paneDim);

	JPanel listPanel=new JPanel();
	listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.X_AXIS));
	listPanel.add(catListScroll);
	listPanel.add(choiceScrollPane);

	getContentPane().setLayout(new BorderLayout());
	getContentPane().add(listPanel, BorderLayout.CENTER);
	getContentPane().add(buttonPanel, BorderLayout.SOUTH);
    }


    /** is called to set the selected choice in 
     * <code>category2DefaultChoice</code>*/
    private void setDefaultChoice(String sel) {
	String category = (String) catList.getSelectedValue();
	if(sel != null){
	    category2DefaultChoice.put(category,sel);
	    changed = true;
	}
    }

    /** is called if the selection of left list has changed, and causes the
     * right one to display the possible choices for the category chosen on
     * the left side
     */
    private void setChoiceList() {
	String selection = (String) catList.getSelectedValue();
	choiceList.setListData(((Set)category2Choices.
				get(selection)).toArray());
	choiceList.setSelectedValue(category2DefaultChoice.
				    get(selection),false);
    }


}    
