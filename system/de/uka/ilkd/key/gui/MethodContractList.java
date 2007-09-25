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

import java.awt.Color;
import java.awt.Component;
import java.awt.FlowLayout;
import java.awt.Font;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.MouseListener;
import java.util.Iterator;
import java.util.List;

import javax.swing.*;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.util.Debug;

public class MethodContractList extends JList implements java.io.Serializable {
    
    /** the model used by this view */
    private MethodContractListModel methodContractListModel;


    MouseListener mouseListener = new MethodContractListMouseListener();


    static final JLabel keyIcon=new JLabel(IconFactory.keyHole(20,20));
    static final JLabel keyClosedIcon
	= new JLabel(IconFactory.keyHoleClosed(20,20));
    static final JLabel keyAlmostClosedIcon
	=new JLabel(IconFactory.keyHoleAlmostClosed(20,20));



    class MethodContractListMouseListener extends MouseAdapter 
	implements java.io.Serializable {
	public void mouseClicked(MouseEvent e) {
	}
    }
    

    public MethodContractList(List ctList){
	setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	methodContractListModel = new MethodContractListModel(ctList);
	if (methodContractListModel.getSize() > 0) {
	    setSelectedIndex(0);
	}       	
	setModel(methodContractListModel);
	setCellRenderer(new IconCellRenderer());
	addMouseListener(mouseListener);		
	updateUI();
    }


    public void updateUI() {
	super.updateUI();
	Font myFont = UIManager.getFont(Config.KEY_FONT_GOAL_LIST_VIEW);
	if (myFont != null) {
	    setFont(myFont);
	} else {
	    Debug.out("goallist: Warning: Use standard font. Could not find font:", 
		      Config.KEY_FONT_GOAL_LIST_VIEW);
	}
    }

    
    public de.uka.ilkd.key.proof.ProofAggregate getProofForCurrentContract() {
	if (getSelectedIndex()<0) {
	    return null;
	}
	Contract mC = (Contract) 
	    methodContractListModel.getElementAt(getSelectedIndex());
	List mCL = mC.getProofs();
	if (mCL.size()!= 0) {
	    return (de.uka.ilkd.key.proof.ProofAggregate) mCL.get(0);
	}	
	return null;
    }

    public Contract getCurrentContract() {
	if (getSelectedIndex()<0) {
	    return null;
	}
	return (Contract) 
	    methodContractListModel.getElementAt(getSelectedIndex());
	
    }


    public static Component makeMethodContractDisplay(OldOperationContract mc,
						      JPanel panel,
						      JTextArea text,
						      JPanel statusPanel,
						      Color c) {
	String mcString = mc.toString();
	text.setText(mcString);
	List proofs = mc.getProofs();
	Iterator it = proofs.iterator();
	statusPanel.removeAll();
	while (it.hasNext()) {
	    ProofAggregate pl = (ProofAggregate) it.next();
	    ProofStatus ps = pl.getStatus();
	    JLabel lab= null;
	    if (ps!=null) {
		if (ps.getProofClosed()) {
		    lab = keyClosedIcon;
		}
		if (ps.getProofClosedButLemmasLeft()) {
		    lab = keyAlmostClosedIcon;
		}
		if (ps.getProofOpen()) {
		    lab = keyIcon;
		}
	    }
	    statusPanel.add(lab);
	}		   		
	text.setBackground(c);
	panel.setBackground(c);
	statusPanel.setBackground(c);
	return panel;
    }


    //INNER CLASSES
        

    static class MethodContractListModel extends AbstractListModel {
    
	private List ctList;

    	MethodContractListModel(List ctList) {
	    this.ctList=ctList;
	}

	public int getSize() {
	    return ctList.size();
	}

	public Object getElementAt(int i) {
	    return ctList.get(i);
	} 


	class MethodContractListProofTreeListener extends ProofTreeAdapter 
	                                implements java.io.Serializable {

	    /** invoked if all goals of the proof are closed
	     */
// 	    public void proofClosed(ProofTreeEvent e) {	   	    
// 		setAttentive(true);
// 		clear();
// 	    }

	}
    }

    class IconCellRenderer extends DefaultListCellRenderer 
	                           implements ListCellRenderer,
				             java.io.Serializable { 

	JPanel panel;
	JPanel statusPanel;
	JTextArea text;
	private Color selBgColor;

	
	public IconCellRenderer() {
	    FlowLayout lay = new FlowLayout();
	    lay.setAlignment(FlowLayout.LEFT);	   	    
	    panel = new JPanel(lay);
	    statusPanel = new JPanel(lay);
	    text = new JTextArea();
	    MethodContractList.this.setToolTipText("Method Contract");
	    panel.add(text);
	    panel.add(statusPanel);
	    text.setEditable(false);
	    text.setCaretPosition(0);
	}
	
	public Component getListCellRendererComponent
	    (JList list,
	     Object value,            // value to display
	     int index,               // cell index
	     boolean isSelected,      // is the cell selected
	     boolean cellHasFocus)    // the list and the cell have the focus
	{
	    if (value instanceof OldOperationContract) {
		if (isSelected && selBgColor==null) {
		    Component sup = super.getListCellRendererComponent
			(list, value, index, isSelected, cellHasFocus);
		    selBgColor = sup.getBackground();
		}
		OldOperationContract mc = (OldOperationContract) value;		
	        return makeMethodContractDisplay(mc, panel, text, statusPanel, 
						 isSelected ? selBgColor 
						            : Color.white);
	    } else {
		return super.getListCellRendererComponent(list, value, 
							  index, isSelected,
							  cellHasFocus);
	    }
	}
	

    }

}
