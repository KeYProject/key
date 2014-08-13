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

package de.uka.ilkd.key.gui.configuration;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.InputStream;
import java.util.Arrays;
import java.util.HashMap;
import java.util.InvalidPropertiesFormatException;
import java.util.Properties;
import java.util.Set;

import javax.swing.BorderFactory;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JFrame;
import javax.swing.JList;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.KeyStroke;
import javax.swing.ListSelectionModel;
import javax.swing.ScrollPaneConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.gui.IconFactory;



public class ChoiceSelector extends JDialog {

    /**
     * 
     */
    private static final long serialVersionUID = -4470713015801365801L;
    private static final String EXPLANATIONS_RESOURCE = "/de/uka/ilkd/key/gui/help/choiceExplanations.xml";
    private ChoiceSettings settings;
    private HashMap<String, String> category2DefaultChoice;
    private HashMap<String, Set<String>> category2Choices;
    private boolean changed=false;


    /** the JList with the categories of choices*/
    private JList catList;
    /** the JList with the choices for one category */
    private JList choiceList;
    private JTextArea explanationArea;
    private static Properties explanationMap;

    /** creates a new ChoiceSelector, using the <code>ChoiceSettings</code>
     * from <code>settings</code> */
    public ChoiceSelector(ChoiceSettings settings) {  
	super(new JFrame(), "Taclet Base Configuration", true);
       	this.settings = settings;
	category2DefaultChoice = settings.getDefaultChoices();
	if(category2DefaultChoice.isEmpty()) {
	    JOptionPane.showConfirmDialog
		(ChoiceSelector.this,
		 "There are no Taclet Options available as the rule-files "+
		 "have not been parsed yet!",
		 "No Options available", 
		 JOptionPane.DEFAULT_OPTION);
	    dispose();
	} else {
	    category2Choices = settings.getChoices();
	    layoutChoiceSelector();
	    setChoiceList();
	    pack();
	    setLocationRelativeTo(null);
	    //setLocation(70, 70);
	    setVisible(true);
	}
    }

    /** creates a new ChoiceSelector */
    public ChoiceSelector(){
	this(ProofSettings.DEFAULT_SETTINGS.getChoiceSettings());
    }

    /** layout */
    protected void layoutChoiceSelector() {
        setIconImage(IconFactory.keyLogo());
        JPanel listPanel=new JPanel();
        listPanel.setLayout(new BorderLayout());
        Object[] cats = category2DefaultChoice.keySet().toArray();
        Arrays.sort(cats);
        {
            catList = new JList(cats);
            catList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
            catList.setSelectedIndex(0);
            catList.addListSelectionListener(new ListSelectionListener() {
                public void valueChanged(ListSelectionEvent e) {
                    setChoiceList();				
                }});
            JScrollPane catListScroll = new
                    JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
                            ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            catListScroll.setBorder(new TitledBorder("Category"));
            catListScroll.getViewport().setView(catList);
            Dimension paneDim = new Dimension(200, 300);
            catListScroll.setPreferredSize(paneDim);
            catListScroll.setMinimumSize(paneDim);
            listPanel.add(catListScroll, BorderLayout.WEST);
        }
        {
            choiceList = new JList();
            choiceList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
            choiceList.setSelectedValue(category2DefaultChoice.get(cats[0]),true);
            choiceList.addListSelectionListener(new ListSelectionListener() {
                public void valueChanged(ListSelectionEvent e) {
                    setDefaultChoice((String) choiceList.getSelectedValue());
                }});

            JScrollPane choiceScrollPane = new 	    
                    JScrollPane(ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
                            ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            choiceScrollPane.getViewport().setView(choiceList);
            choiceScrollPane.setBorder(new TitledBorder("Choice"));
            Dimension paneDim = new Dimension(300, 300);
            choiceScrollPane.setPreferredSize(paneDim);
            choiceScrollPane.setMinimumSize(paneDim);
            listPanel.add(choiceScrollPane, BorderLayout.EAST);
        }
        {
            explanationArea = new JTextArea("Explanation!");
            explanationArea.setEditable(false);
            explanationArea.setLineWrap(true);
            explanationArea.setWrapStyleWord(true);
            JScrollPane scrollPane = new JScrollPane(explanationArea);
            Dimension paneDim = new Dimension(500, 200);
            scrollPane.setPreferredSize(paneDim);
            scrollPane.setMinimumSize(paneDim);
            listPanel.add(scrollPane, BorderLayout.SOUTH);
        }
        JPanel buttonPanel = new JPanel();
        {
            JButton ok = new JButton("OK");
            ok.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    if(changed){
                        int res = JOptionPane.showOptionDialog
                                (ChoiceSelector.this,
                                        "Your changes will become effective when "+
                                                "the next problem is loaded.\n", 
                                                "Taclet Options", 
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
            buttonPanel.add(ok);
            getRootPane().setDefaultButton(ok);	
        }
        {
            final JButton cancel = new JButton("Cancel");
            cancel.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    setVisible(false);
                    dispose();
                }
            });
            ActionListener escapeListener = new ActionListener() {
                public void actionPerformed(ActionEvent event) {
                    if(event.getActionCommand().equals("ESC")) {
                        cancel.doClick();
                    }
                }
            };
            cancel.registerKeyboardAction(
                    escapeListener,
                    "ESC",
                    KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                    JComponent.WHEN_IN_FOCUSED_WINDOW);	
            buttonPanel.add(cancel);
        }

	getContentPane().setLayout(new BorderLayout());
	getContentPane().add(listPanel, BorderLayout.CENTER);
	getContentPane().add(buttonPanel, BorderLayout.SOUTH);
	
	setResizable(false);
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
	choiceList.setListData(category2Choices.
				get(selection).toArray());
	choiceList.setSelectedValue(category2DefaultChoice.
				    get(selection),false);
	explanationArea.setBorder(BorderFactory.createTitledBorder(selection));
	explanationArea.setText(getExplanation(selection));
	explanationArea.setCaretPosition(0);
    }

    /**
     * <p>
     * Returns the explanation for the given category.
     * </p>
     * <p>
     * This method should be public and static because it is independent
     * from the {@link JDialog} and it is also used by the eclipse projects.
     * </p>
     * @param category The category for which the explanation is requested.
     * @return The explanation for the given category.
     */
    public static String getExplanation(String category) {
        synchronized (ChoiceSelector.class) {
            if(explanationMap == null) {
                explanationMap = new Properties();
                InputStream is = ChoiceSelector.class.getResourceAsStream(EXPLANATIONS_RESOURCE);
                try {
                    if (is == null) {
                        throw new FileNotFoundException(EXPLANATIONS_RESOURCE + " not found");
                    }
                    explanationMap.loadFromXML(is);
                } catch (InvalidPropertiesFormatException e) {
                    System.err.println("Cannot load help message in rule view (malformed XML).");
                    e.printStackTrace();
                } catch (IOException e) {
                    System.err.println("Cannot load help messages in rule view.");
                    e.printStackTrace();
                } 
            }
        }
        String result = explanationMap.getProperty(category);
        if(result == null) {
            result = "No explanation for " + category + " available.";
        }
        
        return result;
    }


}