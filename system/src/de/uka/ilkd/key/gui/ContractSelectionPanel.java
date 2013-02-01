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


package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.MouseListener;
import java.util.Arrays;
import java.util.Comparator;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;


/**
 * A panel for selecting contracts.
 */
class ContractSelectionPanel extends JPanel {
    
    /**
     * 
     */
    private static final long serialVersionUID = 1681223715264203991L;
    private final Services services;
    private final JList contractList;
    private final TitledBorder border;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    
    
    /**
     * Creates a contract selection panel containing the specified contracts.
     */
    public ContractSelectionPanel(Services services, 
	                          boolean multipleSelection) {
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        this.services = services;
        
        //create scroll pane
        JScrollPane scrollPane = new JScrollPane();
        border = new TitledBorder("Contracts");
        scrollPane.setBorder(border);
        Dimension scrollPaneDim = new Dimension(700, 500);
        scrollPane.setPreferredSize(scrollPaneDim);
        scrollPane.setMinimumSize(scrollPaneDim);
        add(scrollPane);
        
        //create contract list
        contractList = new JList();
        contractList.setSelectionMode(
                multipleSelection 
                ? ListSelectionModel.MULTIPLE_INTERVAL_SELECTION 
                : ListSelectionModel.SINGLE_SELECTION);
        contractList.addListSelectionListener(new ListSelectionListener() {
            public void valueChanged(ListSelectionEvent e) {
		if(contractList.isSelectionEmpty()) {
		    contractList.setSelectedIndex(e.getFirstIndex());
		}
	    }
        });
        final Services serv = services;
        contractList.setCellRenderer(new DefaultListCellRenderer() {
            /**
             * 
             */
            private static final long serialVersionUID = 9066658130231994408L;
            private final Font PLAINFONT = getFont().deriveFont(Font.PLAIN);
            
	    public Component getListCellRendererComponent(
                                		    JList list,
                                		    Object value,
                                		    int index,
                                		    boolean isSelected,
                                		    boolean cellHasFocus) {
		Contract contract = (Contract) value;
		Component supComp 
		    	= super.getListCellRendererComponent(list, 
		    					     value, 
		    					     index, 
		    					     isSelected, 
		    					     cellHasFocus);		
		
		//create label and enclosing panel
		JLabel label = new JLabel();
		label.setText(contract.getHTMLText(serv));
		label.setFont(PLAINFONT);
		FlowLayout lay = new FlowLayout();
		lay.setAlignment(FlowLayout.LEFT);
		JPanel result = new JPanel(lay);
		result.add(label);
		label.setVerticalAlignment(SwingConstants.TOP);
		
		//set background color
		result.setBackground(supComp.getBackground());

		//set border
		TitledBorder border = new TitledBorder(
				BorderFactory.createEtchedBorder(),
                                contract.getDisplayName());

                Font borderFont = border.getTitleFont();
                if (borderFont == null) { // MS Windows issues
                    borderFont = result.getFont();
                    if (borderFont == null) {
                        borderFont = PLAINFONT;
                    }
                }
		border.setTitleFont(borderFont.deriveFont(Font.BOLD));
		result.setBorder(border);
		
		return result;
	    }
        });
        scrollPane.setViewportView(contractList);        
    }
    
        
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public synchronized void addMouseListener(MouseListener ml) {
        contractList.addMouseListener(ml);
    }
    
    
    public void addListSelectionListener(ListSelectionListener lsl) {
	contractList.addListSelectionListener(lsl);
    }
    
    
    public void setContracts(Contract[] contracts, String title) {
        //sort contracts by id (for the user's convenience)
        Arrays.sort(contracts, new Comparator<Contract> () {
            public int compare(Contract c1, Contract c2) {
                return c1.id() - c2.id();
            }
        });
        
        contractList.setListData(contracts);
        contractList.setSelectedIndex(0);
        if(title != null) {
            border.setTitle(title);
        }
        updateUI();
    }
    
    
    public void setContracts(ImmutableSet<Contract> contracts, String title) {
	setContracts(contracts.toArray(new Contract[contracts.size()]), title);
    }
     
    
    public Contract getContract() {
        final Object[] selection = contractList.getSelectedValues();
        if(selection.length == 0) {
            return null;
        } else if(selection.length == 1) {
            return (Contract) selection[0];
        } else {
            ImmutableSet<FunctionalOperationContract> contracts 
            	= DefaultImmutableSet.<FunctionalOperationContract>nil();
            for(Object contract : selection) {
        	contracts = contracts.add((FunctionalOperationContract) contract);
            }        
            return services.getSpecificationRepository()
                           .combineOperationContracts(contracts);
        }
    }
}
