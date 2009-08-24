// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.*;
import java.util.*;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.ProofStatus;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.OperationContract;


public final class ProofManagementDialog extends JDialog {
    
    private static final ImageIcon keyIcon 
        = IconFactory.keyHole(20, 20);
    private static final ImageIcon keyAlmostClosedIcon 
        = IconFactory.keyHoleAlmostClosed(20, 20);
    private static final ImageIcon keyClosedIcon
        = IconFactory.keyHoleClosed(20, 20);
    
    private static ProofManagementDialog instance;
    private static boolean startedProof;

    private InitConfig initConfig;
    private Services services;
    private SpecificationRepository specRepos;

    private Map<ProgramMethod,Icon> methodIcons;
    private ClassTree classTree;
    private OperationContractSelectionPanel contractPanel;
    private JButton startButton;
    private JButton cancelButton;
    
    
        

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private ProofManagementDialog(InitConfig initConfig, 
	    	      	          String title, 
	    	      	          ProgramMethod defaultPm) {
	super(Main.getInstance(), title, true);
	this.initConfig = initConfig;
	this.services   = initConfig.getServices();
	this.specRepos  = initConfig.getServices().getSpecificationRepository();
	
	//determine default
	if(defaultPm == null) {
	    Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
	    final KeYJavaType[] kjtsarr 
	    	= kjts.toArray(new KeYJavaType[kjts.size()]);
	    Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
		public int compare(KeYJavaType o1, KeYJavaType o2) {
		    return o1.getFullName().compareTo(o2.getFullName());
		}
	    });
	    outer: for(KeYJavaType kjt : kjtsarr) {
		ImmutableList<ProgramMethod> pms 
			= services.getJavaInfo()
				  .getAllProgramMethodsLocallyDeclared(kjt);
		for(ProgramMethod pm : pms) {
		    if(!specRepos.getOperationContracts(pm).isEmpty()) {
			defaultPm = pm;
			break outer;
		    }
		}
	    }	
	}

	//create class tree
	methodIcons = new HashMap<ProgramMethod,Icon>();
	classTree = new ClassTree(true, 
				  true, 
				  null, 
				  defaultPm, 
				  services, 
				  methodIcons);
	classTree.addTreeSelectionListener(new TreeSelectionListener() {
	    public void valueChanged(TreeSelectionEvent e) {
		DefaultMutableTreeNode selectedNode 
			= (DefaultMutableTreeNode) 
				e.getPath().getLastPathComponent();
		ClassTree.Entry entry 
			= (ClassTree.Entry) selectedNode.getUserObject();
		if(entry.pm != null) {
		    showPOsFor(entry.pm);
		} else {
		    clearPOList();
		}
	    }
	});
	
	//create list panel
	JPanel listPanel = new JPanel();
	listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.X_AXIS));
	getContentPane().add(listPanel);
	
	//create class scroll pane
	JScrollPane classScrollPane = new JScrollPane(classTree);
	classScrollPane.setBorder(new TitledBorder("Methods"));
	Dimension classScrollPaneDim = new Dimension(200, 400);
	classScrollPane.setPreferredSize(classScrollPaneDim);
	classScrollPane.setMinimumSize(classScrollPaneDim);
	listPanel.add(classScrollPane);	

	//create contract panel
	contractPanel = new OperationContractSelectionPanel(
				services, 
				"Contracts",
				false);
	contractPanel.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e){                
		if(e.getClickCount() == 2){
		    startButton.doClick();
		}
	    }
	});
	listPanel.add(contractPanel);

	//create button panel
	JPanel buttonPanel = new JPanel();
	buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
	Dimension buttonDim = new Dimension(140, 27);
        buttonPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE, 
                                                 (int)buttonDim.getHeight() 
                                                     + 10));
	getContentPane().add(buttonPanel);

	//create "start proof" button
	startButton = new JButton("Start Proof");
	startButton.setPreferredSize(buttonDim);
	startButton.setMinimumSize(buttonDim);
	startButton.setEnabled(false);
	startButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) { 
                ProofOblInput po = createPOForSelectedContract();
                if(po != null) {
                    setVisible(false);                    
                    findOrStartProof(po);
                }
	    }
	});
	buttonPanel.add(startButton);
	getRootPane().setDefaultButton(startButton);

	//create "cancel" button
	cancelButton = new JButton("Cancel");
	cancelButton.setPreferredSize(buttonDim);
	cancelButton.setMinimumSize(buttonDim);
	cancelButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		setVisible(false);
	    }
	});
	buttonPanel.add(cancelButton);
        ActionListener escapeListener = new ActionListener() {
            public void actionPerformed(ActionEvent event) {
                if(event.getActionCommand().equals("ESC")) {
                    cancelButton.doClick();
                }
            }
        };
        cancelButton.registerKeyboardAction(
                            escapeListener,
                            "ESC",
                            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
                            JComponent.WHEN_IN_FOCUSED_WINDOW);
        
        //complete default selection
        if(defaultPm != null) {
            showPOsFor(defaultPm);
        }

	//show
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));	
	pack();
	setLocation(70, 70);
    }
    
    
    /**
     * Shows the dialog and preselects the passed method.
     */
    public static void showInstance(InitConfig initConfig, 
	    			    ProgramMethod defaultPm) {
	if(instance == null
           || instance.initConfig != initConfig
           || !instance.initConfig.equals(initConfig)
           || defaultPm != null) {
            
            if(instance != null){
                instance.dispose();
                
                //============================================
                // cumbersome but necessary code providing a workaround for a memory leak 
                // in Java, see: http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6497929
                instance.initConfig = null;
                instance.services = null;
                instance.specRepos = null;
                instance.methodIcons = null;
                instance.classTree = null;
                instance.contractPanel = null;
                instance.startButton = null;
                instance.cancelButton = null;
                //============================================
            }
            
            instance = new ProofManagementDialog(initConfig, 
            			     		 "Proof Management", 
            			     		 defaultPm);
        }
	startedProof = false;
	instance.updateStartButton();
	instance.updateMethodIcons();
        instance.setVisible(true);
    }
    

    /**
     * Shows the dialog.
     */
    public static void showInstance(InitConfig initConfig) {
        //show
	showInstance(initConfig, null);
    }

    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private void showPOsFor(ProgramMethod pm) {
	contractPanel.setContracts(pm);
	updateStartButton();
    }
    
    
    private void clearPOList() {
	contractPanel.setContracts(DefaultImmutableSet.<OperationContract>nil());
	updateStartButton();
    }    
    
    
    private ProofOblInput createPOForSelectedContract() {
	OperationContract contract = contractPanel.getContract();
	return contract == null 
	       ? null 
	       : new ContractPO(initConfig, contract);
    }
    
    
    private Proof findPreferablyClosedProof(ProofOblInput po) {
        ImmutableSet<Proof> proofs = specRepos.getProofs(po);
        
        //no proofs?
        if(proofs.size() == 0) {
            return null;
        }
        
        //try to find closed proof
        for(Proof proof : proofs) {
            if(proof.mgt().getStatus().getProofClosed()) {
                return proof;
            }
        }
        
        //just take any proof
        return proofs.iterator().next();
    }    
    
    
    private void findOrStartProof(ProofOblInput po) {
        Proof proof = findPreferablyClosedProof(po);
        if(proof == null) {
            ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
            try {
                pi.startProver(initConfig, po);
            } catch(ProofInputException exc) {
        	new ExceptionDialog(Main.getInstance(), exc);
            }
        } else {
            Main.getInstance().mediator().setProof(proof);
        }
        startedProof = true;
    }
    
    
    private void updateStartButton() {
	final ProofOblInput po = createPOForSelectedContract();
	if(po == null) {
	    startButton.setText("No Contract");
            startButton.setIcon(null);
	    startButton.setEnabled(false);
	} else {
	    final Proof proof = findPreferablyClosedProof(po);
	    if(proof == null) {
		startButton.setText("Start Proof");
		startButton.setIcon(null);
	    } else {
		final ProofStatus status = proof.mgt().getStatus();
		if(status.getProofOpen()) {
		    startButton.setText("Go to Proof");		    
		    startButton.setIcon(keyIcon);
		} else if(status.getProofClosedButLemmasLeft()) {
		    startButton.setText("Go to Proof");
		    startButton.setIcon(keyAlmostClosedIcon);
		} else {
		    assert status.getProofClosed();
		    startButton.setText("Go to Proof");
		    startButton.setIcon(keyClosedIcon);
		}
	    }
	    startButton.setEnabled(true);
	}
    }
    
    
    private void updateMethodIcons() {
	Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
	for(KeYJavaType kjt : kjts) {
	    ImmutableList<ProgramMethod> pms 
	    	= services.getJavaInfo().getAllProgramMethods(kjt);
	    for(ProgramMethod pm : pms) {
		ImmutableSet<OperationContract> contracts 
			= specRepos.getOperationContracts(pm);
		boolean startedProving = false;
		boolean allClosed = true;		
		boolean lemmasLeft = false;
		for(OperationContract contract : contracts) {
		    ContractPO po = new ContractPO(initConfig, contract);
		    Proof proof = findPreferablyClosedProof(po);
		    if(proof == null) {
			allClosed = false;
		    } else {
			startedProving = true;
			ProofStatus status = proof.mgt().getStatus();
			if(status.getProofOpen()) {
			    allClosed = false;
			} else if(status.getProofClosedButLemmasLeft()) {
			    lemmasLeft = true;
			}		    
		    }
		}
		methodIcons.put(pm, startedProving
			            ? (allClosed
			               ? (lemmasLeft 
			                  ? keyAlmostClosedIcon 
			                  : keyClosedIcon)
			               : keyIcon)
			             : null);
	    }
	}
	classTree.updateUI();
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public static boolean startedProof() {
	return startedProof;
    }
}
