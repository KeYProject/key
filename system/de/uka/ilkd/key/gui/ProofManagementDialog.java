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

import java.awt.Component;
import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.event.*;
import java.util.*;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.*;
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
import de.uka.ilkd.key.util.Pair;


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

    private JTabbedPane tabbedPane;
    private Map<Pair<ProgramMethod,KeYJavaType>,Icon> methodIcons;
    private ClassTree classTree;
    private JList proofList;
    private OperationContractSelectionPanel contractPanelByMethod;
    private OperationContractSelectionPanel contractPanelByProof;
    private JButton startButton;
    private JButton cancelButton;
        

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private ProofManagementDialog(InitConfig initConfig, String title) {
	super(Main.getInstance(), title, true);
	this.initConfig = initConfig;
	this.services   = initConfig.getServices();
	this.specRepos  = initConfig.getServices().getSpecificationRepository();
	
	//create class tree
	methodIcons = new HashMap<Pair<ProgramMethod,KeYJavaType>,Icon>();
	classTree = new ClassTree(true, true, services, methodIcons);
	classTree.addTreeSelectionListener(new TreeSelectionListener() {
	    public void valueChanged(TreeSelectionEvent e) {
		DefaultMutableTreeNode selectedNode 
			= (DefaultMutableTreeNode) 
				e.getPath().getLastPathComponent();
		ClassTree.Entry entry 
			= (ClassTree.Entry) selectedNode.getUserObject();
		if(entry.pm != null) {
		    showPOsFor(entry.pm, entry.kjt);
		} else {
		    clearPOList();
		}
	    }
	});
	
	//create proof list
	proofList = new JList();
	proofList.setCellRenderer(new DefaultListCellRenderer() {
	     public Component getListCellRendererComponent(JList list, 
		     					   Object value, 
		     					   int index, 
		     					   boolean isSelected, 
		     					   boolean cellHasFocus) {
		 Component result = super.getListCellRendererComponent(list, 
			 					       value, 
			 					       index, 
			 					       isSelected, 
			 					       cellHasFocus);
		 if(result instanceof JLabel) {
		     ProofStatus ps 
		     	= ((ProofWrapper)value).proof.mgt().getStatus();
		     JLabel label = (JLabel) result;
		     if(ps.getProofClosed()) {
			 label.setIcon(keyClosedIcon);
		     } else if(ps.getProofClosedButLemmasLeft()) {
			 label.setIcon(keyAlmostClosedIcon);
		     } else {
			 assert ps.getProofOpen();
			 label.setIcon(keyIcon);
		     }
		 }
		 return result;
	     }
	});
	proofList.addListSelectionListener(new ListSelectionListener() {
	    public void valueChanged(ListSelectionEvent e) {
		if(proofList.getSelectedValue() != null) {
		    Proof p = ((ProofWrapper)proofList.getSelectedValue()).proof;
		    showPOsFor(p);
		} else {
		    clearPOList();
		}
	    }
	});

	//create method list panel, scroll pane
	JPanel listPanelByMethod = new JPanel();
	listPanelByMethod.setLayout(new BoxLayout(listPanelByMethod, 
						  BoxLayout.X_AXIS));
	JScrollPane classScrollPane = new JScrollPane(classTree);
	classScrollPane.setBorder(new TitledBorder("Methods"));
	Dimension classScrollPaneDim = new Dimension(250, 400);
	classScrollPane.setPreferredSize(classScrollPaneDim);
	classScrollPane.setMinimumSize(classScrollPaneDim);
	listPanelByMethod.add(classScrollPane);
	
	//create proof list panel, scroll pane	
	JPanel listPanelByProof = new JPanel();
	listPanelByProof.setLayout(new BoxLayout(listPanelByProof, 
						 BoxLayout.X_AXIS));	
	JScrollPane proofScrollPane = new JScrollPane(proofList);
	proofScrollPane.setBorder(new TitledBorder("Proofs"));
	proofScrollPane.setPreferredSize(classScrollPaneDim);
	proofScrollPane.setMinimumSize(classScrollPaneDim);
	listPanelByProof.add(proofScrollPane);	
	
	//create contract panel by method
	contractPanelByMethod = new OperationContractSelectionPanel(
				services, 
				"Contracts",
				false);
	contractPanelByMethod.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e){
		if(e.getClickCount() == 2){
		    startButton.doClick();
		}
	    }
	});
	contractPanelByMethod.addListSelectionListener(new ListSelectionListener() {
	    public void valueChanged(ListSelectionEvent e) {
		updateStartButton();
	    }
	});
	listPanelByMethod.add(contractPanelByMethod);
	
	//create contract panel by proof
	contractPanelByProof = new OperationContractSelectionPanel(
				services, 
				"Contracts",
				false);
	contractPanelByProof.addMouseListener(new MouseAdapter() {
	    public void mouseClicked(MouseEvent e){
		updateStartButton();
		if(e.getClickCount() == 2){
		    startButton.doClick();
		}
	    }
	});
	contractPanelByProof.addListSelectionListener(new ListSelectionListener() {
	    public void valueChanged(ListSelectionEvent e) {
		updateStartButton();
	    }
	});
	listPanelByProof.add(contractPanelByProof);	
	
	//create tabbed pane
	tabbedPane = new JTabbedPane();	
        tabbedPane.addTab("By Method", listPanelByMethod);
        tabbedPane.addTab("By Proof", listPanelByProof);
        tabbedPane.addChangeListener(new ChangeListener() {
            public void stateChanged(ChangeEvent e) {
        	updateStartButton();
        	if(proofList.getSelectedIndex() == -1 
                    && proofList.getModel().getSize() > 0) {
        	    proofList.setSelectedIndex(0);
        	}
            }
        });
        getContentPane().add(tabbedPane);

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
 
	//show
        getContentPane().setLayout(new BoxLayout(getContentPane(), 
                                                 BoxLayout.Y_AXIS));	
	pack();
	setLocation(20, 20);
    }
    
    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private static void showInstance(InitConfig initConfig,
	    			     ProgramMethod selectedPM,
	    			     Proof selectedProof) {
	if(instance == null
           || instance.initConfig != initConfig
           || !instance.initConfig.equals(initConfig)) {
            
            if(instance != null){
                instance.dispose();
                
                //============================================
                // cumbersome but necessary code providing a workaround for a memory leak 
                // in Java, see: http://bugs.sun.com/bugdatabase/view_bug.do?bug_id=6497929
                instance.initConfig = null;
                instance.services = null;
                instance.specRepos = null;
                instance.tabbedPane = null;
                instance.proofList = null;
                instance.methodIcons = null;
                instance.classTree = null;
                instance.contractPanelByMethod = null;
                instance.contractPanelByProof = null;
                instance.startButton = null;
                instance.cancelButton = null;
                //============================================
            }
            
            instance = new ProofManagementDialog(initConfig, 
            			     		 "Proof Management");
            //determine own defaults if not given
            if(selectedPM == null) {
        	Services services = initConfig.getServices();
        	Set<KeYJavaType> kjts 
        		= services.getJavaInfo().getAllKeYJavaTypes();
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
        		if(!services.getSpecificationRepository()
        			    .getOperationContracts(pm, kjt).isEmpty()) {
        		    selectedPM = pm;
        		    break outer;
        		}
        	    }
        	}	
            }
        }
	
	startedProof = false;
	instance.updateStartButton();
	instance.updateGlobalStatus();
	if(selectedProof != null) {
	    instance.select(selectedProof);
	}
	if(selectedPM != null) {
	    instance.select(selectedPM);
	}
        instance.setVisible(true);
    }    
    
    
    private OperationContractSelectionPanel getActiveContractPanel() {
	return tabbedPane.getSelectedIndex() == 0 
	       ? contractPanelByMethod 
		       : contractPanelByProof;
    }
    
    
    private void showPOsFor(ProgramMethod pm, KeYJavaType kjt) {
	getActiveContractPanel().setContracts(pm, kjt);
	updateStartButton();
    }
    
    
    private void showPOsFor(Proof p) {
	ImmutableSet<OperationContract> usedContracts 
		= p.mgt().getUsedContracts();
	        
        getActiveContractPanel().setContracts(usedContracts, 
        	                              "Contracts used in proof \"" 
        	                                 + p.name() + "\"");
        updateStartButton();
    }
    
    
    private void clearPOList() {
	getActiveContractPanel().setContracts(
			DefaultImmutableSet.<OperationContract>nil(),
		        "Contracts");
	updateStartButton();
    }
    
    
    private void select(ProgramMethod pm) {
	tabbedPane.setSelectedIndex(0);
	classTree.select(pm);
    }
    
    
    private void select(Proof p) {
	for(int i = 0, n = proofList.getModel().getSize(); i < n; i++) {
	    if(((ProofWrapper) proofList.getModel()
		                        .getElementAt(i))
		                          .proof.equals(p)) {
		tabbedPane.setSelectedIndex(1);		
		proofList.setSelectedIndex(i);
		break;
	    }
	}
    }
    
    
    private ProofOblInput createPOForSelectedContract() {
	OperationContract contract = getActiveContractPanel().getContract();
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
    
    
    private void updateGlobalStatus() {
	//method icons
	Set<KeYJavaType> kjts = services.getJavaInfo().getAllKeYJavaTypes();
	for(KeYJavaType kjt : kjts) {
	    ImmutableList<ProgramMethod> pms 
	    	= services.getJavaInfo().getAllProgramMethods(kjt);
	    for(ProgramMethod pm : pms) {
		ImmutableSet<OperationContract> contracts 
			= specRepos.getOperationContracts(pm, kjt);
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
		methodIcons.put(new Pair<ProgramMethod,KeYJavaType>(pm, kjt), 
			        startedProving
			        ? (allClosed
			           ? (lemmasLeft 
			              ? keyAlmostClosedIcon 
			              : keyClosedIcon)
			           : keyIcon)
			        : null);
	    }
	}
	classTree.updateUI();

	//proof list
	DefaultListModel model = new DefaultListModel();
	for(Proof p : specRepos.getAllProofs()) {
	    model.add(0, new ProofWrapper(p));
	}
	boolean changed;
	if(model.size() != proofList.getModel().getSize()) {
	    changed = true;
	} else {
	    changed = false;
	    for(int i = 0, n = model.size(); i < n; i++) {
		if(!model.get(i).equals(proofList.getModel().getElementAt(i))) {
		    changed = true;
		    break;
		}
	    }
	}
	if(changed) {
	    proofList.setModel(model);
	    proofList.updateUI();
	}
	
	updateStartButton();
    }
    
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    
    /**
     * Shows the dialog and selects the passed method.
     */
    public static void showInstance(InitConfig initConfig,
	    			    ProgramMethod selectedPM) {
	showInstance(initConfig, selectedPM, null);
    }

    
    /**
     * Shows the dialog and selects the passed proof.
     */
    public static void showInstance(InitConfig initConfig, 
	    			    Proof selectedProof) {
	showInstance(initConfig, null, selectedProof);
    }
    
    
    /**
     * Shows the dialog.
     */
    public static void showInstance(InitConfig initConfig) {
	showInstance(initConfig, null, null);
    }    
    
    
    /**
     * Tells whether the last call to a showInstance() method lead to 
     * starting a proof.
     */
    public static boolean startedProof() {
	return startedProof;
    }
    
    
    
    //-------------------------------------------------------------------------
    //inner classes
    //-------------------------------------------------------------------------
    
    private static final class ProofWrapper {
	public final Proof proof;
	
	public ProofWrapper(Proof proof) {
	    this.proof = proof;
	}
	
	@Override
	public String toString() {
	    return proof.name().toString();
	}
	
	@Override
	public boolean equals(Object o) {
	    return o instanceof ProofWrapper
	           && proof.equals(((ProofWrapper)o).proof);
	}
	
	@Override
	public int hashCode() {
	    return proof.hashCode();
	}
    }
}
