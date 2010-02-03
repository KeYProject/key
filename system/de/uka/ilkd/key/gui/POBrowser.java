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
import java.util.Iterator;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.TreeSelectionEvent;
import javax.swing.event.TreeSelectionListener;
import javax.swing.tree.DefaultMutableTreeNode;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;


public class POBrowser extends JDialog {
    
    private static POBrowser instance;

    private InitConfig initConfig;
    private Services services;
    private JavaInfo javaInfo;
    private SpecificationRepository specRepos;

    private ClassTree classTree;
    private JList poList;
    private JButton startButton;
    private JButton cancelButton;
    
    private ProofOblInput po;
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    private POBrowser(InitConfig initConfig, 
	    	      String title, 
	    	      ProgramMethod defaultPm) {
	super(Main.getInstance(), title, true);
	this.initConfig = initConfig;
	this.services   = initConfig.getServices();
	this.javaInfo   = initConfig.getServices().getJavaInfo();
	this.specRepos  = initConfig.getServices().getSpecificationRepository();

	//create class tree
	classTree = new ClassTree(true, true, null, defaultPm, services);
	classTree.addTreeSelectionListener(new TreeSelectionListener() {
	    public void valueChanged(TreeSelectionEvent e) {
		DefaultMutableTreeNode selectedNode 
			= (DefaultMutableTreeNode) 
				e.getPath().getLastPathComponent();
		ClassTree.Entry entry 
			= (ClassTree.Entry) selectedNode.getUserObject();
		if(entry.kjt != null) {
		    showPOsFor(entry.kjt);
		} else if(entry.pm != null) {
		    showPOsFor(entry.pm);
		} else {
		    clearPOList();
		}
	    }
	});

	//create PO list
	poList = new JList();
	poList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
        poList.addMouseListener(new MouseAdapter() {
            public void mouseClicked(MouseEvent e){                
                if(e.getClickCount() == 2){
                   startButton.doClick();
                }
            }
        });
        
	//create list panel
	JPanel listPanel = new JPanel();
	listPanel.setLayout(new BoxLayout(listPanel, BoxLayout.X_AXIS));
	getContentPane().add(listPanel);

	//create class scroll pane
	JScrollPane classScrollPane = new JScrollPane(classTree);
	classScrollPane.setBorder(new TitledBorder("Classes and Operations"));
	Dimension classScrollPaneDim = new Dimension(400, 400);
	classScrollPane.setPreferredSize(classScrollPaneDim);
	classScrollPane.setMinimumSize(classScrollPaneDim);
	listPanel.add(classScrollPane);

	//create PO scroll pane
	JScrollPane poScrollPane = new JScrollPane(poList);
	poScrollPane.setBorder(new TitledBorder("Proof Obligations"));
	Dimension poScrollPaneDim = new Dimension(250, 400);
	poScrollPane.setPreferredSize(poScrollPaneDim);
	poScrollPane.setMinimumSize(poScrollPaneDim);
	listPanel.add(poScrollPane);

	//create button panel
	JPanel buttonPanel = new JPanel();
	buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
	Dimension buttonDim = new Dimension(100, 27);
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
                po = createPO();
                if(po != null) {
                    setVisible(false);
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
     * Shows the PO browser and preselects the passed method.
     */
    public static POBrowser showInstance(InitConfig initConfig, 
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
                instance.javaInfo = null;
                instance.specRepos = null;
                instance.classTree = null;
                instance.poList = null;
                instance.startButton = null;
                instance.cancelButton = null;
                instance.po = null;
                //============================================
            }
            
            instance = new POBrowser(initConfig, 
            			     "Proof Obligation Browser", 
            			     defaultPm);
        }
        instance.po = null;
        instance.setVisible(true);
        return instance;
    }
    

    /**
     * Shows the PO browser.
     */
    public static POBrowser showInstance(InitConfig initConfig) {
	return showInstance(initConfig, null);
    }

    
    
    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    private void showPOsFor(KeYJavaType kjt) {
	ListOfString pos = SLListOfString.EMPTY_LIST;

	//BehaviouralSubtypingInv
	if(specRepos.getClassInvariants(kjt).size() > 0
	   && javaInfo.getDirectSuperTypes(kjt).size() > 0) {
	    pos = pos.append("BehaviouralSubtypingInv");
	}

/*        
	//BehaviouralSubtypingOp
	ListOfProgramMethod pms = javaInfo.getAllProgramMethods(kjt);
	IteratorOfProgramMethod it = pms.iterator();
	boolean foundContract = false;
	while(it.hasNext()) {
	    ProgramMethod pm = it.next();
	    if(specRepos.getOperationContracts(pm).size() > 0) {
		foundContract = true;
		break;
	    }
	}
	if(foundContract && javaInfo.getDirectSuperTypes(kjt).size() > 0) {
	    pos = pos.append("BehaviouralSubtypingOp");
	}	
*/
        
	//show
	poList.setListData(pos.toArray());
	if(pos.size() > 0) {
	    poList.setSelectedIndex(0);
	    startButton.setEnabled(true);
	} else {
	    startButton.setEnabled(false);
	}
    }
    
    
    private void showPOsFor(ProgramMethod pm) {
	ListOfString pos = SLListOfString.EMPTY_LIST;

/*        
	//BehaviouralSubtypingOpPair
	if(specRepos.getOperationContracts(pm).size() > 0 
	   && javaInfo.getDirectSuperTypes(pm.getContainerType()).size() > 0) {
	    pos = pos.append("BehaviouralSubtypingOpPair");
	}
*/
	
	//StrongOperationContract
	if(specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append("StrongOperationContract");
	}
	
	//PreservesInv
	pos = pos.append("PreservesInv");
	
	//PreservesOwnInv
	if(specRepos.getClassInvariants(pm.getKeYJavaType()).size() > 0) {
	    pos = pos.append("PreservesOwnInv");
	}
	
	//EnsuresPost
	if(specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append("EnsuresPost");
	}

        //RespectsWorkingSpace
        if(specRepos.getOperationContracts(pm).size() > 0 && 
                (ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile && 
                		((RTSJProfile) ProofSettings.DEFAULT_SETTINGS.getProfile()).memoryConsumption())) {
            pos = pos.append("RespectsWorkingSpace");           
        }
        
	//RespectsModifies
	if(specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append("RespectsModifies");	    
	}
	
	//implemented by mbender for jmltest
	//Specification Extraction
        if(specRepos.getOperationContracts(pm).size() > 0) {
            pos = pos.append("SpecificationExtraction");
        }
	
	//PreservesGuard
	pos = pos.append("PreservesGuard");
	
	//show
	poList.setListData(pos.toArray());
	if(pos.size() > 0) {
	    poList.setSelectedValue("EnsuresPost", true);
	    if(poList.getSelectedIndex() == -1) {
		poList.setSelectedIndex(0);
	    }
	    startButton.setEnabled(true);
	} else {
	    startButton.setEnabled(false);
	}
    }
    
    
    private void clearPOList() {
	poList.setListData(new Object[0]);
	startButton.setEnabled(false);
    }    
    
    
    /**
     * Lets the user select a supertype of subKJT in a dialog window.
     */
    private KeYJavaType askUserForSupertype(KeYJavaType subKJT, 
	    				    JavaInfo javaInfo) {
	//collect supertypes
	SetOfKeYJavaType superKJTs = SetAsListOfKeYJavaType.EMPTY_SET;
	IteratorOfKeYJavaType it = javaInfo.getAllSupertypes(subKJT).iterator();
	while(it.hasNext()) {
	    superKJTs = superKJTs.add(it.next());
	}
	
	//ask user
        ClassSelectionDialog dlg = new ClassSelectionDialog(
        		"Please select a supertype",
        		"Supertypes of " + subKJT.getName(),
        		superKJTs,
        		false);
        if(!dlg.wasSuccessful()) {
            return null;
        }
        
        //return selection
        SetOfKeYJavaType selectedKJTs = dlg.getSelection();
        if(selectedKJTs.size() == 0) {
            return null;
        } else {
            return selectedKJTs.iterator().next();
        }
    }
    
    
    private ProofOblInput createPO() {
	ClassTree.Entry selectedEntry = classTree.getSelectedEntry();
	String poString = (String) poList.getSelectedValue();
	
	if (poString.equals("BehaviouralSubtypingInv")) {
            assert selectedEntry.kjt != null;
            return createBehaviouralSubtypingInvPO(selectedEntry.kjt);
        } else if (poString.equals("BehaviouralSubtypingOp")) {
            assert selectedEntry.kjt != null;
            return createBehaviouralSubtypingOpPO(selectedEntry.kjt);
        } else if (poString.equals("BehaviouralSubtypingOpPair")) {
            assert selectedEntry.pm != null;
            return createBehaviouralSubtypingOpPairPO(selectedEntry.pm);
        } else if (poString.equals("StrongOperationContract")) {
            assert selectedEntry.pm != null;
            return createStrongOperationContractPO(selectedEntry.pm);
        } else if (poString.equals("PreservesInv")) {
            assert selectedEntry.pm != null;
            return createPreservesInvPO(selectedEntry.pm);
        } else if (poString.equals("PreservesOwnInv")) {
            assert selectedEntry.pm != null;
            return createPreservesOwnInvPO(selectedEntry.pm);
        } else if (poString.equals("EnsuresPost")) {
            assert selectedEntry.pm != null;
            return createEnsuresPostPO(selectedEntry.pm);
        } else if (poString.equals("RespectsWorkingSpace")) {
            assert selectedEntry.pm != null;
            return createRespectsWorkingSpacePO(selectedEntry.pm);
        } else if (poString.equals("RespectsModifies")) {
            assert selectedEntry.pm != null;
            return createRespectsModifiesPO(selectedEntry.pm);
        } else if (poString.equals("PreservesGuard")) {
            assert selectedEntry.pm != null;
            return createPreservesGuardPO(selectedEntry.pm);
        } else if (poString.equals("SpecificationExtraction")) {
            assert selectedEntry.pm != null;
            return createSpecExtPO(selectedEntry.pm);
        } else
            assert false;
        return null;
    }

    
    private ProofOblInput createBehaviouralSubtypingInvPO(KeYJavaType kjt) {
	KeYJavaType superKJT = askUserForSupertype(kjt, javaInfo);
	if(superKJT != null) {
	    return new BehaviouralSubtypingInvPO(initConfig, 
		         			 kjt, 
		         			 superKJT);
	} else {
	    return null;
	}
    }

    
    private ProofOblInput createBehaviouralSubtypingOpPO(KeYJavaType kjt) {
	assert false;
	return null; //TODO    
    }
    
    
    private ProofOblInput createBehaviouralSubtypingOpPairPO(ProgramMethod pm) {
	assert false;
	return null; //TODO
    }
    
    
    private ProofOblInput createStrongOperationContractPO(ProgramMethod pm) {
	ContractConfigurator cc = new ContractConfigurator(this,
						           services,
						           pm,
						           null,
						           true,
						           true,
						           true);
	if(cc.wasSuccessful()) {
	    return new StrongOperationContractPO(initConfig, 
		    				 cc.getContract(), 
		    				 cc.getAssumedInvs(), 
		    				 cc.getEnsuredInvs());
	} else {
	    return null;
	}
    }
 
    
    private ProofOblInput createPreservesInvPO(ProgramMethod pm) {
	ContractConfigurator cc = new ContractConfigurator(this, 
						           services, 
						           pm, 
						           null, 
						           false, 
						           true, 
						           true);
	if(cc.wasSuccessful()) {
	    return new PreservesInvPO(initConfig, 
                                      pm, 
                                      cc.getAssumedInvs(), 
                                      cc.getEnsuredInvs());
	} else {
	    return null;
	}
    }
    
    
    private ProofOblInput createPreservesOwnInvPO(ProgramMethod pm) {
	return new PreservesOwnInvPO(initConfig, pm);
    }
    
    
    private ProofOblInput createEnsuresPostPO(ProgramMethod pm) {
	ContractConfigurator cc = new ContractConfigurator(this,
						           services, 
						           pm, 
						           null, 
						           true,
						           true,
						           false);
	if(cc.wasSuccessful()) {
	    return new EnsuresPostPO(initConfig, 
                                     cc.getContract(), 
                                     cc.getAssumedInvs());
	} else {
	    return null;
	}
    }
    
    private ProofOblInput createRespectsWorkingSpacePO(ProgramMethod pm) {
        ContractConfigurator cc = new ContractConfigurator(this,
                                                           services, 
                                                           pm, 
                                                           null, 
                                                           true,
                                                           true,
                                                           false);
        if(cc.wasSuccessful()) {
            return new RespectsWorkingSpacePO(initConfig, 
                                     cc.getContract(), 
                                     cc.getAssumedInvs());
        } else {
            return null;
        }
    }
    
    
    private ProofOblInput createRespectsModifiesPO(ProgramMethod pm) {
	ContractConfigurator cc = new ContractConfigurator(this,
						           services,
						           pm,
						           null,
						           true,
						           true,
						           false);
	if(cc.wasSuccessful()) {
	    return new RespectsModifiesPO(initConfig, 
                                          cc.getContract(), 
                                          cc.getAssumedInvs());
	} else {
	    return null;
	}
    }
    
    
    private ProofOblInput createPreservesGuardPO(ProgramMethod pm) {
        //let the user select the guarded invariants 
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                                        "Please select the guarded invariants",
                                        initConfig.getServices(), 
                                        false, 
                                        pm.getContainerType());
        if(dlg.wasSuccessful()) {
            //let the user select the guard classes
            SetOfKeYJavaType allKJTs = SetAsListOfKeYJavaType.EMPTY_SET;
            final Iterator<KeYJavaType> it = javaInfo.getAllKeYJavaTypes().iterator();
            while(it.hasNext()) {
        	allKJTs = allKJTs.add(it.next());
            }
            ClassSelectionDialog dlg2
                    = new ClassSelectionDialog("Please select the guard",
                                               "Available classes",
                                               allKJTs,
                                               pm.getContainerType(),
                                               true);
            if(dlg2.wasSuccessful()) {
        	return new PreservesGuardPO(initConfig, 
					    pm, 
					    dlg.getSelection(),
					    dlg2.getSelection());
            } else {
        	return null;
            }
        } else {
            return null;
        }
    }
    
//    implemented by mbender for jmltest
    private ProofOblInput createSpecExtPO(ProgramMethod pm) {
        ContractConfigurator cc = new ContractConfigurator(this,
                                                           services, 
                                                           pm, 
                                                           null, 
                                                           true,
                                                           true,
                                                           false);
        if(cc.wasSuccessful()) {
            return new SpecExtPO(initConfig, 
                                     cc.getContract(), 
                                     cc.getAssumedInvs(),pm);
        } else {
            return null;
        }
    }
    
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public ProofOblInput getAndClearPO(){
        ProofOblInput result = po;
        po = null; //to prevent memory leaks
        return result;
    }
    
}
