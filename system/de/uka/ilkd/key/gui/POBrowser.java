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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
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
	ImmutableList<String> pos = ImmutableSLList.<String>nil();
        
	//show
	poList.setListData(pos.toArray(new String[pos.size()]));
	if(pos.size() > 0) {
	    poList.setSelectedIndex(0);
	    startButton.setEnabled(true);
	} else {
	    startButton.setEnabled(false);
	}
    }
    
    
    private void showPOsFor(ProgramMethod pm) {
	ImmutableList<String> pos = ImmutableSLList.<String>nil();
	
	//PreservesInv
	pos = pos.append("PreservesInv");
	
	//PreservesOwnInv
	if(specRepos.getClassInvariants(pm.getContainerType()).size() > 0) {
	    pos = pos.append("PreservesOwnInv");
	}
	
	//EnsuresPost
	if(specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append("EnsuresPost");
	}
	

	//show
	poList.setListData(pos.toArray(new String[pos.size()]));
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
	ImmutableSet<KeYJavaType> superKJTs = DefaultImmutableSet.<KeYJavaType>nil();
	Iterator<KeYJavaType> it = javaInfo.getAllSupertypes(subKJT).iterator();
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
        ImmutableSet<KeYJavaType> selectedKJTs = dlg.getSelection();
        if(selectedKJTs.size() == 0) {
            return null;
        } else {
            return selectedKJTs.iterator().next();
        }
    }
    
    
    private ProofOblInput createPO() {
	ClassTree.Entry selectedEntry = classTree.getSelectedEntry();
	String poString = (String) poList.getSelectedValue();
	
	if (poString.equals("PreservesInv")) {
            assert selectedEntry.pm != null;
            return createPreservesInvPO(selectedEntry.pm);
        } else if (poString.equals("PreservesOwnInv")) {
            assert selectedEntry.pm != null;
            return createPreservesOwnInvPO(selectedEntry.pm);
        } else if (poString.equals("EnsuresPost")) {
            assert selectedEntry.pm != null;
            return createEnsuresPostPO(selectedEntry.pm);
        } else
            assert false;
        return null;
    }

    
    
    private ProofOblInput createPreservesInvPO(ProgramMethod pm) {
	ContractConfigurator cc = new ContractConfigurator(this, 
						           services, 
						           pm, 
						           null, 
						           false,
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
    
        
    
    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    public ProofOblInput getAndClearPO(){
        ProofOblInput result = po;
        po = null; //to prevent memory leaks
        return result;
    }
}
