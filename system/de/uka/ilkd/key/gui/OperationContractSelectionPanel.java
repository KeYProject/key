// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
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
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * A panel for selecting operation contracts.
 */
class OperationContractSelectionPanel extends JPanel {
    
    private final Services services;
    private final JList contractList;
    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------    
    
    /**
     * Creates a contract selection panel containing the specified contracts.
     */
    public OperationContractSelectionPanel(Services services,
                                           String title,
                                           boolean multipleSelection) {
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        this.services = services;
        
        //create scroll pane
        JScrollPane scrollPane = new JScrollPane();
        scrollPane.setBorder(new TitledBorder(title));
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
            private final Font PLAINFONT = getFont().deriveFont(Font.PLAIN);
            
	    public Component getListCellRendererComponent(
                                		    JList list,
                                		    Object value,
                                		    int index,
                                		    boolean isSelected,
                                		    boolean cellHasFocus) {
		OperationContract contract = (OperationContract) value;
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
		border.setTitleFont(border.getTitleFont()
					  .deriveFont(Font.BOLD));
		result.setBorder(border);
		
		return result;
	    }
        });
        scrollPane.setViewportView(contractList);        
    }
    
        
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private ImmutableSet<OperationContract> collectContracts(
	    					ProgramMethod pm, 
                                                Modality modality) {
        SpecificationRepository specRepos 
                = services.getSpecificationRepository();
        ImmutableSet<OperationContract> result;
        if(modality != null) {
            result = specRepos.getOperationContracts(pm, modality);
            
            //in box modalities, diamond contracts may be applied as well
            if(modality == Modality.BOX) {
                result = result.union(services.getSpecificationRepository()
                                              .getOperationContracts(pm, Modality.DIA));
            }
        } else {
            result = specRepos.getOperationContracts(pm);
        }
        return result;
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public void addMouseListener(MouseListener ml) {
        contractList.addMouseListener(ml);
    }
    
    
    public void setContracts(ImmutableSet<OperationContract> contracts) {
        //sort contracts alphabetically (for the user's convenience)
        OperationContract[] contractsArray 
        	= contracts.toArray(new OperationContract[contracts.size()]);
        Arrays.sort(contractsArray, new Comparator<OperationContract> () {
            public int compare(OperationContract c1, OperationContract c2) {
                return c1.getName().compareTo(c2.getName());
            }
        });
        
        contractList.setListData(contractsArray);
        contractList.setSelectedIndex(0);        
    }
    
    
    public void setContracts(ProgramMethod pm, Modality modality) {
	setContracts(collectContracts(pm, modality));
    }
    
    
    
    public void setContracts(ProgramMethod pm) {
	setContracts(collectContracts(pm, null));
    }    
    
    
    public OperationContract getContract() {
        Object[] selection = contractList.getSelectedValues();
        ImmutableSet<OperationContract> contracts 
            = DefaultImmutableSet.<OperationContract>nil();
        for(Object contract : selection) {
            contracts = contracts.add((OperationContract) contract);
        }        
        return contracts.isEmpty() 
               ? null 
               : services.getSpecificationRepository()
                         .combineContracts(contracts);
    }
}
