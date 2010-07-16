package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.JButton;
import javax.swing.JPanel;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.proofobligation.DefaultPOProvider;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;

public class JavaDefaultUsedSpecificationDialog extends
        UsedSpecificationsDialog {

    private JButton ensuresPostButton;
    private JButton preservesInvButton;
    private JButton respectsModifiesButton;

    public JavaDefaultUsedSpecificationDialog(Services services,
	    ImmutableSet<ContractWithInvs> contractApps) {
	super(services, contractApps);
    }
    
    protected void createPOButtonPanel(Services services, 
	    ImmutableSet<ContractWithInvs> atomicContractApps, 
	    JPanel buttonPanel,
	    Dimension largeButtonDim, Dimension extraLargeButtonDim) {
	final DefaultPOProvider poProvider = (services.getProof() != null ? services
	        .getProof().getSettings().getProfile()
	        : ProofSettings.DEFAULT_SETTINGS.getProfile()).getPOProvider();

	// create "EnsuresPost" button
	ensuresPostButton = new JButton("EnsuresPost");
	ensuresPostButton.setPreferredSize(largeButtonDim);
	ensuresPostButton.setMinimumSize(largeButtonDim);
	ensuresPostButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		ContractWithInvs cwi = (ContractWithInvs) contractAppList
		        .getSelectedValue();
		InitConfig initConfig = Main.getInstance().mediator()
		        .getSelectedProof().env().getInitConfig();
		ProofOblInput po = poProvider.createEnsuresPostPO(initConfig,
		        cwi.contract, cwi.assumedInvs);
		findOrStartProof(initConfig, po);
		setVisible(false);
		dispose();
	    }
	});
	buttonPanel.add(ensuresPostButton);

	// create "PreservesInv" button
	preservesInvButton = new JButton("PreservesInv");
	preservesInvButton.setPreferredSize(largeButtonDim);
	preservesInvButton.setMinimumSize(largeButtonDim);
	preservesInvButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		ContractWithInvs cwi = (ContractWithInvs) contractAppList
		        .getSelectedValue();
		InitConfig initConfig = Main.getInstance().mediator()
		        .getSelectedProof().env().getInitConfig();
		ProofOblInput po = poProvider.createPreservesInvPO(initConfig,
		        cwi.contract.getProgramMethod(), cwi.assumedInvs,
		        cwi.ensuredInvs);
		findOrStartProof(initConfig, po);
		setVisible(false);
		dispose();
	    }
	});
	buttonPanel.add(preservesInvButton);

	// create "RespectsModifies" button
	respectsModifiesButton = new JButton("RespectsModifies");
	respectsModifiesButton.setPreferredSize(extraLargeButtonDim);
	respectsModifiesButton.setMinimumSize(extraLargeButtonDim);
	respectsModifiesButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		ContractWithInvs cwi = (ContractWithInvs) contractAppList
		        .getSelectedValue();
		InitConfig initConfig = Main.getInstance().mediator()
		        .getSelectedProof().env().getInitConfig();
		ProofOblInput po = poProvider.createRespectsModifiesPO(
		        initConfig, cwi.contract, cwi.assumedInvs);
		findOrStartProof(initConfig, po);
		setVisible(false);
	    }
	});
	buttonPanel.add(respectsModifiesButton);
    
	 //disable PO buttons if no specifications
        if(atomicContractApps.size() == 0) {
            ensuresPostButton.setEnabled(false);
            preservesInvButton.setEnabled(false);
            respectsModifiesButton.setEnabled(false);
        } else {
            updatePOButtons();
        }
    }
    
    protected void updatePOButtons() {
	InitConfig initConfig = Main.getInstance().mediator()
	        .getSelectedProof().env().getInitConfig();

	DefaultPOProvider poProvider = initConfig.getProfile().getPOProvider();

	ContractWithInvs cwi = (ContractWithInvs) contractAppList
	        .getSelectedValue();

	// ensuresPost
	ProofOblInput ensuresPostPO = poProvider.createEnsuresPostPO(
	        initConfig, cwi.contract, cwi.assumedInvs);
	Proof ensuresPostProof = findPreferablyClosedProof(ensuresPostPO);
	if (ensuresPostProof == null) {
	    ensuresPostButton.setIcon(null);
	} else if (ensuresPostProof.mgt().getStatus().getProofOpen()) {
	    ensuresPostButton.setIcon(keyIcon);
	} else if (ensuresPostProof.mgt().getStatus()
	        .getProofClosedButLemmasLeft()) {
	    ensuresPostButton.setIcon(keyAlmostClosedIcon);
	} else {
	    assert ensuresPostProof.mgt().getStatus().getProofClosed();
	    ensuresPostButton.setIcon(keyClosedIcon);
	}

	// preservesInv
	ProofOblInput preservesInvPO = poProvider.createPreservesInvPO(
	        initConfig, cwi.contract.getProgramMethod(), cwi.assumedInvs,
	        cwi.ensuredInvs);
	Proof preservesInvProof = findPreferablyClosedProof(preservesInvPO);
	if (preservesInvProof == null) {
	    preservesInvButton.setIcon(null);
	} else if (preservesInvProof.mgt().getStatus().getProofOpen()) {
	    preservesInvButton.setIcon(keyIcon);
	} else if (preservesInvProof.mgt().getStatus()
	        .getProofClosedButLemmasLeft()) {
	    preservesInvButton.setIcon(keyAlmostClosedIcon);
	} else {
	    assert preservesInvProof.mgt().getStatus().getProofClosed();
	    preservesInvButton.setIcon(keyClosedIcon);
	}

	// respectsModifies
	ProofOblInput respectsModifiesPO = poProvider.createRespectsModifiesPO(
	        initConfig, cwi.contract, cwi.assumedInvs);
	Proof respectsModifiesProof = findPreferablyClosedProof(respectsModifiesPO);
	if (respectsModifiesProof == null) {
	    respectsModifiesButton.setIcon(null);
	} else if (respectsModifiesProof.mgt().getStatus().getProofOpen()) {
	    respectsModifiesButton.setIcon(keyIcon);
	} else if (respectsModifiesProof.mgt().getStatus()
	        .getProofClosedButLemmasLeft()) {
	    respectsModifiesButton.setIcon(keyAlmostClosedIcon);
	} else {
	    assert respectsModifiesProof.mgt().getStatus().getProofClosed();
	    respectsModifiesButton.setIcon(keyClosedIcon);
	}
    }

}
