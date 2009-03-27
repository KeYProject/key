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

import javax.swing.BorderFactory;
import javax.swing.BoxLayout;
import javax.swing.DefaultListCellRenderer;
import javax.swing.JLabel;
import javax.swing.JList;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.ListSelectionModel;
import javax.swing.SwingConstants;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetAsListOfOperationContract;
import de.uka.ilkd.key.speclang.SetOfOperationContract;


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
                                           SetOfOperationContract contracts,
                                           String title,
                                           boolean multipleSelection) {
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        this.services = services;
        
        //create scroll pane
        JScrollPane scrollPane = new JScrollPane();
        scrollPane.setBorder(new TitledBorder(title));
        Dimension scrollPaneDim = new Dimension(800, 500);
        scrollPane.setPreferredSize(scrollPaneDim);
        scrollPane.setMinimumSize(scrollPaneDim);
        add(scrollPane);
        
        //sort contracts alphabetically (for the user's convenience)
        OperationContract[] contractsArray = contracts.toArray();
        Arrays.sort(contractsArray, new Comparator<OperationContract> () {
            public int compare(OperationContract c1, OperationContract c2) {
                return c1.getName().compareTo(c2.getName());
            }
        });
        
        //create contract list
        contractList = new JList();
        contractList.setSelectionMode(
                multipleSelection 
                ? ListSelectionModel.MULTIPLE_INTERVAL_SELECTION 
                : ListSelectionModel.SINGLE_SELECTION);
        contractList.setListData(contractsArray);
        contractList.setSelectedIndex(0);
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
    
    
    private static SetOfOperationContract collectContracts(Services services,
                                                           ProgramMethod pm, 
                                                           Modality modality) {
        SpecificationRepository specRepos 
                = services.getSpecificationRepository();
        SetOfOperationContract result;
        if(modality != null) {
            result = specRepos.getOperationContracts(pm, modality);
            
            //in box modalities, diamond contracts may be applied as well
            if(modality == Op.BOX) {
                result = result.union(services.getSpecificationRepository()
                                              .getOperationContracts(pm, Op.DIA));
            }
        } else {
            result = specRepos.getOperationContracts(pm);
        }
        assert result.size() > 0;
        return result;
    }
    
    
    /**
     * Creates a contract selection panel containing all contracts for the 
     * specified operation with the specified modality.
     */
    public OperationContractSelectionPanel(Services services,
                                           ProgramMethod pm,
                                           Modality modality,
                                           boolean multipleSelection) {
        this(services, 
             collectContracts(services, pm, modality),  
             "Contracts for \"" 
                + pm.getFullName()
                + "\""
                + (modality != null ? " (" + modality + ")" : ""),
             multipleSelection);
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public void addMouseListener(MouseListener ml) {
        contractList.addMouseListener(ml);
    }
    
    
    public OperationContract getOperationContract() {
        Object[] selection = contractList.getSelectedValues();
        SetOfOperationContract contracts 
            = SetAsListOfOperationContract.EMPTY_SET;
        for(Object contract : selection) {
            contracts = contracts.add((OperationContract) contract);
        }        
        return services.getSpecificationRepository()
                       .combineContracts(contracts);
    }
}
