// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.FlowLayout;
import java.awt.Frame;
import java.awt.event.*;

import javax.swing.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.BlockContract;

// TODO Clean up.
public class BlockContractConfigurator extends JDialog {

    private static final long serialVersionUID = 4882043118399402599L;

    private BlockContractSelectionPanel contractPanel;
    private JButton okButton;
    private JButton cancelButton;

    private boolean successful = false;

    public BlockContractConfigurator(final JDialog owner,
                                     final Services services,
                                     final BlockContract[] contracts,
                                     final String title,
                                     final boolean allowMultipleContracts)
    {
        super(owner, "Block Contract Configurator", true);
        init(services, contracts, title, allowMultipleContracts);
    }

    public BlockContractConfigurator(final Frame owner,
                                     final Services services,
                                     final BlockContract[] contracts,
                                     final String title,
                                     final boolean allowMultipleContracts)
    {
        super(owner, "Block Contract Configurator", true);
        init(services, contracts, title, allowMultipleContracts);
    }

    private void init(final Services services,
                      final BlockContract[] contracts,
                      final String title,
                      final boolean allowMultipleContracts)
    {
        initContractPanel(services, contracts, title, allowMultipleContracts);
        initButtonPanelAndOkayAndCancelButtons();
        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
        pack();
        setLocation(70, 70);
        setVisible(true);
    }

    private void initContractPanel(final Services services,
                                   final BlockContract[] contracts,
                                   final String title,
                                   final boolean allowMultipleContracts)
    {
        contractPanel = new BlockContractSelectionPanel(services, allowMultipleContracts);
        contractPanel.setContracts(contracts, title);
        contractPanel.addMouseListener(new MouseAdapter() {
            public void mouseClicked(MouseEvent e){
                if(e.getClickCount() == 2){
                    okButton.doClick();
                }
            }
        });
        contractPanel.setMinimumSize(new Dimension(800, 500));
        getContentPane().add(contractPanel);
    }

    private void initButtonPanelAndOkayAndCancelButtons()
    {
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(100, 27);
        buttonPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE, (int) buttonDim.getHeight() + 10));
        getContentPane().add(buttonPanel);
        initOkayButton(buttonDim, buttonPanel);
        initCancelButton(buttonDim, buttonPanel);
    }

    private void initOkayButton(final Dimension dimension, final JPanel container)
    {
        okButton = new JButton("OK");
        okButton.setPreferredSize(dimension);
        okButton.setMinimumSize(dimension);
        okButton.addActionListener(new ActionListener() {
            public void actionPerformed(final ActionEvent event) {
                successful = true;
                setVisible(false);
                dispose();
            }
        });
        container.add(okButton);
        getRootPane().setDefaultButton(okButton);
    }

    private void initCancelButton(final Dimension dimension, final JPanel container)
    {
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(dimension);
        cancelButton.setMinimumSize(dimension);
        cancelButton.addActionListener(new ActionListener() {
            public void actionPerformed(final ActionEvent event) {
                successful = false;
                setVisible(false);
                dispose();
            }
        });
        container.add(cancelButton);
        ActionListener escapeListener = new ActionListener() {
            public void actionPerformed(ActionEvent event) {
                if (event.getActionCommand().equals("ESC")) {
                    cancelButton.doClick();
                }
            }
        };
        cancelButton.registerKeyboardAction(
            escapeListener,
            "ESC",
            KeyStroke.getKeyStroke(KeyEvent.VK_ESCAPE, 0),
            JComponent.WHEN_IN_FOCUSED_WINDOW
        );
    }

    /**
     * Tells whether the user clicked "ok".
     */
    public boolean wasSuccessful() {
        return successful;
    }

    /**
     * Returns the selected contract.
     */
    public BlockContract getContract() {
        return contractPanel.getContract();
    }

}