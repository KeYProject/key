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

import java.awt.BorderLayout;
import java.awt.GridBagConstraints;
import java.awt.GridBagLayout;
import java.awt.Insets;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.util.List;

import javax.swing.*;

import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.BasicTask;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.ContractSet;

public class UsedMethodContractsList extends JDialog {

    private BasicTask invokedNode;
    private KeYMediator mediator;
    private ContractSelectionPanel mCL;
    private Contract contract = null;
    private static UsedMethodContractsList instance = null;
    private ContractSet cs = null;
    private boolean firstPO = false;
    private boolean dispose = true;
    private JButton jump = null;

    // Some instances are kept, some are created on the fly and
    // garbage collected
    
    public static UsedMethodContractsList getInstance(KeYMediator mediator, 
            ContractSet contractSet) {
	if(instance == null)
	  instance = new UsedMethodContractsList(null, mediator, "Choose DL Contract");
        instance.setupWindow(null, contractSet, true, false, false);
	return instance;
    }

    public static UsedMethodContractsList getInstance(KeYMediator mediator) {
	if(instance == null)
	  instance = new UsedMethodContractsList(null,  mediator, "Choose DL Contract");
        instance.setupWindow(mediator.getSelectedProof().getBasicTask(),
           mediator.getSelectedProof().getBasicTask().getAllDLMethodContracts(),
	   false, false, true);
	return instance;
    }

    private void setupWindow(BasicTask invokedNode,
                             ContractSet contractSet,
			     boolean firstPO,
			     boolean dispose,
			     boolean jumpEnable) {
	this.invokedNode = invokedNode;
	this.cs = contractSet;
	this.firstPO = firstPO;
	this.dispose = dispose;
	this.mCL.setContracts(cs);
	this.jump.setEnabled(jumpEnable);
    }

    public UsedMethodContractsList(BasicTask invokedNode, 
				   KeYMediator med) {
	this(invokedNode, med, "Used Specifications");
    }
    
    
    private UsedMethodContractsList(BasicTask invokedNode, 
				   KeYMediator med, String title) {
	super(new JFrame(), title);
	if(invokedNode != null)
          setDefaultCloseOperation(DISPOSE_ON_CLOSE);
	else
	  setDefaultCloseOperation(HIDE_ON_CLOSE);
	this.invokedNode=invokedNode;
	this.mediator=med;
	setModal(true);
	ContractSet allMC = invokedNode != null ? invokedNode.getAllMethodContracts() : null;		
	mCL = new ContractSelectionPanel(allMC, true);		
	JScrollPane scroll = new JScrollPane();
	scroll.setViewportView(mCL);
	scroll.setPreferredSize(new java.awt.Dimension(400,500));	
	getContentPane().setLayout(new BorderLayout());
	getContentPane().add(scroll, BorderLayout.CENTER);
	JButton cancel = new JButton("Cancel");
	cancel.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if(dispose)
		      ((JDialog)((JButton)e.getSource())
		       .getTopLevelAncestor()).dispose();
		    else{
		      setVisible(false);
		    }
		}});
        jump = new JButton("Go To Proof");
	jump.addActionListener(new ActionListener() {
	        public void actionPerformed(ActionEvent e) {
		    ((JDialog)((JButton)e.getSource())
		     .getTopLevelAncestor()).dispose();
		    openTaskForCurrentContract();
		}});
	JButton open = new JButton("Start New Proof");
	open.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    if (dispose) {
		      ((JDialog)((JButton)e.getSource())
		       .getTopLevelAncestor()).dispose();			   
		        Runnable proofLoader = new Runnable() {
		 	      public void run() {
			 	openNewProofForCurrentContract();
			      }
			  };
		      KeYMediator.invokeAndWait(proofLoader);
		    } else {
		      if(firstPO) {
	                contract = mCL.getCurrentSelection();
		        setVisible(false);
		      }else{
		        setVisible(false);
		        Runnable proofLoader = new Runnable() {
		 	      public void run() {
			 	openNewProofForCurrentContract();
			      }
			  };
		        KeYMediator.invokeAndWait(proofLoader);
		      }
		    }
		}});
	

	JPanel p = new JPanel(new GridBagLayout());
	GridBagConstraints c = new GridBagConstraints();
		
	c.insets = new Insets(5,20,5,20);
	c.gridx = 0;
	p.add(jump, c);    
		
	c.gridx = 1;
	p.add(open, c);    

	c.gridx = 2;
	p.add(cancel, c);    
	p.setAlignmentY(JPanel.BOTTOM_ALIGNMENT);
		
	getContentPane().add(p, BorderLayout.SOUTH);
	getContentPane().add(new JLabel("Specifications:"), 
				BorderLayout.NORTH);
	pack();
	getContentPane().add(scroll);
    }
    
    public void dispose() {
        mediator.freeModalAccess(this);
        super.dispose();
    }

    public void setVisible(boolean show) {
        if(show)
          mediator.requestModalAccess(this);
	else
          mediator.freeModalAccess(this);
        super.setVisible(show);
    }

    public Contract getContract() {
      // You can only ask once for a contract
      Contract res = contract;
      contract = null;
      return res;
    }

    private void openTaskForProof(ProofAggregate p) {
        mediator.setProof(p.getFirstProof());
    }


    public void openTaskForCurrentContract() {
        Contract mC = mCL.getCurrentSelection();
        List mCL = mC.getProofs();
        if (mCL.size()!= 0) {
            openTaskForProof((ProofAggregate)mCL.get(0));
        }	
    }

    public void openNewProofForCurrentContract() {
	Contract mC = mCL.getCurrentSelection();
	if (mC==null) return;
	ProofOblInput poin = mC.getProofOblInput(invokedNode.proof());
	if (poin==null) return;
	ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	try {
	    pi.startProver(invokedNode.proof().env(), poin);
	} catch(ProofInputException e) {
	    //too bad
	}
    }

}
