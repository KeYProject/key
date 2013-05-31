// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.gui.nodeviews;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import javax.swing.*;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;

public abstract class InsertionTacletBrowserMenuItem extends JMenu
 implements TacletMenuItem {

    /**
     * 
     */
    private static final long serialVersionUID = 1874640339950617746L;
    /** all taclet apps the user can choose from */
    private Collection<TacletAppListItem> insertionTaclets;
    /** the added action listeners */
    private List<ActionListener> listenerList = new LinkedList<ActionListener>();
    /** the notation info to pretty print the taclet apps */
    protected NotationInfo notInfo;
    /** the parent frame of the selection dialog to be displayed */
    protected JFrame parent;
    /** the selected taclet to be applied */
    private TacletApp selectedTaclet;
    /** the services */
    protected Services services;
    
    /** the base title; used title = basetitle + ( nrOfItems ) */
    private String baseTitle;

    public InsertionTacletBrowserMenuItem(String title, JFrame parent, 
            NotationInfo notInfo, Services services) {
        
        super(title);
        this.baseTitle = title;
        this.parent = parent;
        this.notInfo = notInfo;
        this.services = services;
        
        insertionTaclets = createInsertionList();
        
        final JMenuItem menuItem = new JMenuItem("Open Dialog");
        menuItem.addActionListener(new ActionListener() {

            public void actionPerformed(ActionEvent e) {              
                    openDialog();
            }
            
        });                  
        
        menuItem.setToolTipText("Browse applicable taclets.");
        
        add(menuItem);
        addSeparator();
    }

    /**
     * returns the list where the tacletappItems are stored
     * (allows easy exchange for e.g. a sorted list)
     * default: is filo
     */
    protected Collection<TacletAppListItem> createInsertionList() {
        return new LinkedList<TacletAppListItem>();
    }
    
    
    /**
     * adds a new taclet to be displayed by this component
     * it is assumed that the app has been tested before by 
     * {@link #isResponsible}  
     * @param app the TacletApp to be added
     */
    public void add(TacletApp app) {
        insertionTaclets.add(createListItem(app));
        final DefaultTacletMenuItem appItem = 
            new DefaultTacletMenuItem(this, app, notInfo);
        appItem.addActionListener(new ActionListener() {
    
            public void actionPerformed(ActionEvent e) {
                processTacletSelected(e);
            }
            
        });
        add(appItem);
        setText(baseTitle + " (" + getAppSize() + (getAppSize() != 1 ? " items" : " item") +")");
    }


    public void addActionListener(ActionListener listener) {
        listenerList.add(listener);
    }

    protected abstract Sequent checkTaclet(Taclet t);

    /** returns the selected taclet to be applied */
    public TacletApp connectedTo() {        
        return selectedTaclet;
    }

    public int getAppSize() {
        return insertionTaclets.size();
    }

    /**
     * tests if this class is responsible for the given taclet
     * @param t the Taclet to be checked
     * @return true if this item implementation shall be used
     */
    public boolean isResponsible(Taclet t) {
        return checkTaclet(t) != null;
    }

    /**
     * opens the selection dialog displaying all hidden formulas
     * in a list and allowing the user to select the one to be added     
     */
    public void openDialog() {
            final JDialog dialog      = 
                new JDialog(parent, getText(), true);
            
            final JList selectionList = new JList(insertionTaclets.toArray());
            
            final JScrollPane scrollPane = 
                new JScrollPane(selectionList, ScrollPaneConstants.VERTICAL_SCROLLBAR_AS_NEEDED, 
                        ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
            scrollPane.setPreferredSize(new Dimension(300,100));
            scrollPane.setMinimumSize(new Dimension(150,50));
           
            
            selectionList.
                setSelectionMode(ListSelectionModel.SINGLE_SELECTION);  
                 
            if (getAppSize()>0) { // should always be true
                selectionList.setSelectedIndex(0);
            }
            
            
            final JTextArea displayHiddenFormula = new JTextArea();

            final Object selectedValue = selectionList.getSelectedValue();
            displayHiddenFormula.
              setText(selectedValue == null ? "" :                  
                          ((TacletAppListItem)selectedValue).longDescription());
    
            displayHiddenFormula.setCaretPosition(0);
            
            displayHiddenFormula.setEditable(false);
            
            selectionList.addListSelectionListener(new ListSelectionListener()
            {
                public void valueChanged(ListSelectionEvent e) {                       
                    if (e.getSource() instanceof JList) {
                        final JList list = (JList)e.getSource();
                        if (list.getSelectedIndex()>=0) {           
                            if (list.getSelectedValue() instanceof TacletAppListItem) {
                                displayHiddenFormula.
                                setText(((TacletAppListItem)list.getSelectedValue()).
                                        longDescription());
                            }                                   
                        } else {
                            displayHiddenFormula.setText("");
                        }
                        displayHiddenFormula.setCaretPosition(0);
                    }
                }

            });
            
            final JScrollPane formulaDisplaySP = new JScrollPane(displayHiddenFormula);
            
            final JSplitPane split = new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,
                         scrollPane, formulaDisplaySP) {
                /**
                             * 
                             */
                            private static final long serialVersionUID = -6688343484818325411L;

                public void setUI(javax.swing.plaf.SplitPaneUI ui) {
                    try{ super.setUI(ui); } catch(NullPointerException e) 
                    {Debug.out("Exception thrown by class Main at setUI"); }
                }
            }; // work around bug in 
    //      com.togethersoft.util.ui.plaf.metal.OIMetalSplitPaneUI
            selectedTaclet = null;
                                   
            final JButton cancel = new JButton("Cancel");
            cancel.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {
                    selectedTaclet = null;
                    dialog.setVisible(false);
                    dialog.dispose();
                }          
            });
                        
            final JButton apply  = new JButton("Apply");
            apply.addActionListener(new ActionListener() {
                public void actionPerformed(ActionEvent e) {                
                    final TacletAppListItem selectedItem = 
                        (TacletAppListItem)selectionList.getSelectedValue();
                    
                    if (selectedItem == null) { // should never be true
                        selectedTaclet = null;
                    } else {
                        selectedTaclet = selectedItem.getTacletApp();
                    }
                    
                    dialog.setVisible(false);
                    dialog.dispose();
                    processTacletSelected(new ActionEvent
                            (InsertionTacletBrowserMenuItem.this, 0, ""));
                }           
            });
            
            final JPanel buttonPanel = new JPanel();
            buttonPanel.setLayout(new FlowLayout());
            
            buttonPanel.add(apply);
            buttonPanel.add(cancel);
    
            dialog.getContentPane().setLayout(new BorderLayout());
            
            dialog.getContentPane().add(split, BorderLayout.CENTER);
            dialog.getContentPane().add(buttonPanel, BorderLayout.SOUTH);                
                   
            dialog.setSize(500, 250);
           
            dialog.setVisible(true); 
            
        }

    protected void processTacletSelected(ActionEvent e) {
        for (final ActionListener al : listenerList) {
            al.actionPerformed(e);
        }
    }

    public void removeActionListener(ActionListener listener) {
        listenerList.remove(listener);
    }
    
    public TacletAppListItem createListItem(TacletApp app) {
        return new TacletAppListItem(app, checkTaclet(app.taclet()), 
                notInfo, services);
    }
    
    /**
     * inner class to pretty print the formulas to be added
     */
    static class TacletAppListItem {
        private final TacletApp app;
        private final NotationInfo notInfo;
        private final Services services;
        private final Sequent seq;
        
        public TacletAppListItem(TacletApp app, Sequent seq, NotationInfo notInfo, 
                Services services) {
            this.app      = app;
            this.seq = seq;
            this.notInfo  =  notInfo;
            this.services =  services;
        }
        
        public TacletApp getTacletApp() {
            return app;
        }
        
        public String shortDescription() {
            return longDescription();
        }

        public String longDescription() {
            final LogicPrinter printer = 
                new LogicPrinter(new ProgramPrinter(), notInfo, services, true);
            printer.setInstantiation(app.instantiations());
            printer.printSequent(seq);
            return printer.toString();
        }

        public String toString() {
            return longDescription();            
        }
    }

}
