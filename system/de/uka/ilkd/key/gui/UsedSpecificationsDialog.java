// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.util.ArrayList;

import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionEvent;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.proofobligation.DefaultPOProvider;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.speclang.OperationContract;

public class UsedSpecificationsDialog extends JDialog {

    protected static final ImageIcon keyIcon = IconFactory.keyHole(20, 20);
    protected static final ImageIcon keyAlmostClosedIcon = IconFactory
	    .keyHoleAlmostClosed(20, 20);
    protected static final ImageIcon keyClosedIcon = IconFactory.keyHoleClosed(
	    20, 20);

    private final Services services;
    protected final JList contractAppList;
    private JButton cancelButton;
    private ArrayList<POButtonAction> poButtonActions;

    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    protected UsedSpecificationsDialog(
	    	Services services,
	    	ImmutableSet<ContractWithInvs> contractApps) {
	super(Main.getInstance(), "Specifications Used in the Proof", true);
	this.services = services;

	// break contract apps down to atomic contracts
	ImmutableSet<ContractWithInvs> atomicContractApps 
		= DefaultImmutableSet.<ContractWithInvs> nil();
	for (ContractWithInvs cwi : contractApps) {
	    for (OperationContract atomicContract : 
			services.getSpecificationRepository()
			        .splitContract(cwi.contract)) {
		ContractWithInvs atomicCwi 
			= new ContractWithInvs(atomicContract, 
					       cwi.assumedInvs, 
					       cwi.ensuredInvs);
		atomicContractApps = atomicContractApps.add(atomicCwi);
	    }
	}

	// create scroll pane
	JScrollPane scrollPane = new JScrollPane();
	Dimension scrollPaneDim = new Dimension(800, 500);
	scrollPane.setPreferredSize(scrollPaneDim);
	scrollPane.setMinimumSize(scrollPaneDim);
	getContentPane().add(scrollPane);

	// create contract app list
	contractAppList = new JList();
	contractAppList.setSelectionMode(ListSelectionModel.SINGLE_SELECTION);
	contractAppList.setListData(atomicContractApps
	        .toArray(new ContractWithInvs[atomicContractApps.size()]));
	contractAppList.setSelectedIndex(0);
	contractAppList.addListSelectionListener(new ListSelectionListener() {
	    public void valueChanged(ListSelectionEvent e) {
		if (contractAppList.isSelectionEmpty()) {
		    contractAppList.setSelectedIndex(e.getFirstIndex());
		}
		updatePOButtons();
	    }
	});
	contractAppList.setCellRenderer(new DefaultListCellRenderer() {
	    private final Font PLAINFONT = getFont().deriveFont(Font.PLAIN);

	    public Component getListCellRendererComponent(JList list,
		    Object value, int index, boolean isSelected,
		    boolean cellHasFocus) {
		ContractWithInvs cwi = (ContractWithInvs) value;
		Component supComp = super.getListCellRendererComponent(list,
		        value, index, isSelected, cellHasFocus);

		// create label and enclosing panel
		JLabel label = new JLabel();
		label.setText(cwi
		        .getHTMLText(UsedSpecificationsDialog.this.services));
		label.setFont(PLAINFONT);
		FlowLayout lay = new FlowLayout();
		lay.setAlignment(FlowLayout.LEFT);
		JPanel result = new JPanel(lay);
		result.add(label);
		label.setVerticalAlignment(SwingConstants.TOP);

		// set background color
		result.setBackground(supComp.getBackground());

		// set border
		TitledBorder border = new TitledBorder(BorderFactory
		        .createEtchedBorder(), cwi.contract.getDisplayName());
                Font borderFont = border.getTitleFont();
                if (borderFont == null) { // MS Windows/JDK7 issues
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
	scrollPane.setViewportView(contractAppList);

	// create button panel
	JPanel buttonPanel = new JPanel();
	buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
	Dimension buttonDim = new Dimension(115, 27);
	Dimension largeButtonDim = new Dimension(145, 27);
	Dimension extraLargeButtonDim = new Dimension(170, 27);
	getContentPane().add(buttonPanel);
        buttonPanel.add(new JLabel("Prove that selected spec: "));

	createPOButtonPanel(services, atomicContractApps, buttonPanel,
	        largeButtonDim, extraLargeButtonDim);

	// create "cancel" button
	cancelButton = new JButton("Cancel");
	cancelButton.setPreferredSize(buttonDim);
	cancelButton.setMinimumSize(buttonDim);
	cancelButton.addActionListener(new ActionListener() {
	    public void actionPerformed(ActionEvent e) {
		setVisible(false);
	    }
	});

	buttonPanel.add(cancelButton);
	getRootPane().setDefaultButton(cancelButton);
	ActionListener escapeListener = new ActionListener() {
	    public void actionPerformed(ActionEvent event) {
		if (event.getActionCommand().equals("ESC")) {
		    cancelButton.doClick();
		}
	    }
	};
	cancelButton.registerKeyboardAction(escapeListener, "ESC",
	        KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
	        JComponent.WHEN_IN_FOCUSED_WINDOW);

	// show
	getContentPane().setLayout(
	        new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
	pack();
	setLocation(70, 70);
	setVisible(true);
    }

    protected Proof findPreferablyClosedProof(ProofOblInput po) {
	ImmutableSet<Proof> proofs = services.getSpecificationRepository()
	        .getProofs(po);

	// no proofs?
	if (proofs.size() == 0) {
	    return null;
	}

	// try to find closed proof
	for (final Proof proof : proofs) {
	    if (proof.mgt().getStatus().getProofClosed()) {
		return proof;
	    }
	}

	// just take any proof
	return proofs.iterator().next();
    }

    protected void findOrStartProof(InitConfig initConfig, ProofOblInput po) {
	Proof proof = findPreferablyClosedProof(po);
	if (proof == null) {
	    ProblemInitializer pi = getProfile(initConfig.getServices()).
	    	createProblemInitializer(Main.getInstance());
	    try {
		pi.startProver(initConfig, po);
	    } catch (ProofInputException exc) {
		exc.printStackTrace(System.out);
	    }
	} else {
	    Main.getInstance().mediator().setProof(proof);
	}
    }

    protected void createPOButtonPanel(Services services,
	    final ImmutableSet<ContractWithInvs> atomicContractApps,
	    JPanel buttonPanel, Dimension largeButtonDim,
	    Dimension extraLargeButtonDim) {
	poButtonActions = new ArrayList<POButtonAction>();

	final DefaultPOProvider poProvider = getProfile(services).getPOProvider();

	final ImmutableList<String> poNames = poProvider
	        .getRequiredCorrectnessProofObligationsForOperationContracts();

	for (final String poName : poNames) {

	    final JButton poButton = new JButton(poName);
	    poButton.setPreferredSize(largeButtonDim);
	    poButton.setMinimumSize(largeButtonDim);

	    poButtonActions.add(new POButtonAction(atomicContractApps, poName,
		    poProvider));
	    poButton.setAction(poButtonActions.get(poButtonActions.size() - 1));

	    buttonPanel.add(poButton);

	}

	// disable PO buttons if no specifications
	if (atomicContractApps.size() != 0) {
	    updatePOButtons();
	}
    }

    protected Profile getProfile(Services services) {
	return (services.getProof() != null ? services
	        .getProof().getSettings().getProfile()
	        : ProofSettings.DEFAULT_SETTINGS.getProfile());
    }

    protected void updatePOButtons() {
	for (POButtonAction action : poButtonActions) {
	    action.update();
	}
    }

    private final class POButtonAction extends AbstractAction {
	private final ImmutableSet<ContractWithInvs> atomicContractApps;
	private final String poName;
	private final DefaultPOProvider poProvider;

	private POButtonAction(
	        ImmutableSet<ContractWithInvs> atomicContractApps,
	        String poName, DefaultPOProvider poProvider) {

	    super(poName);

	    this.atomicContractApps = atomicContractApps;
	    this.poName = poName;
	    this.poProvider = poProvider;

	    setEnabled(atomicContractApps.size() != 0);
	}

	public void actionPerformed(ActionEvent e) {
	    ContractWithInvs cwi = (ContractWithInvs) contractAppList
		    .getSelectedValue();
	    InitConfig initConfig = Main.getInstance().mediator()
		    .getSelectedProof().env().getInitConfig();
	    ProofOblInput po = poProvider.createOperationContractPOByName(
		    poName, cwi, initConfig);

	    assert po != null;

	    findOrStartProof(initConfig, po);

	    setVisible(false);
	    dispose();
	}

	public void update() {
	    InitConfig initConfig = Main.getInstance().mediator()
		    .getSelectedProof().env().getInitConfig();

	    ContractWithInvs cwi = (ContractWithInvs) contractAppList
		    .getSelectedValue();

	    ProofOblInput po = poProvider.createOperationContractPOByName(
		    poName, cwi, initConfig);

	    assert po != null;

	    Proof poProof = findPreferablyClosedProof(po);
	    if (poProof == null) {
		putValue(Action.LARGE_ICON_KEY, null);
	    } else if (poProof.mgt().getStatus().getProofOpen()) {
		putValue(Action.LARGE_ICON_KEY, keyIcon);
	    } else if (poProof.mgt().getStatus().getProofClosedButLemmasLeft()) {
		putValue(Action.LARGE_ICON_KEY, keyAlmostClosedIcon);
	    } else {
		assert poProof.mgt().getStatus().getProofClosed();
		putValue(Action.LARGE_ICON_KEY, keyClosedIcon);
	    }
	}
    }

}
