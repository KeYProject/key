/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.utilities.GuiUtilities;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.Contract;


public class ContractConfigurator extends JDialog {

    /**
     *
     */
    private static final long serialVersionUID = 4002043118399402599L;
    private ContractSelectionPanel contractPanel;
    private JButton okButton;
    private JButton cancelButton;

    private boolean successful = false;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public ContractConfigurator(JDialog owner, Services services, Contract[] contracts,
            String title, boolean allowMultipleContracts) {
        super(owner, "Contract Configurator", true);
        init(services, contracts, title, allowMultipleContracts);
    }


    public ContractConfigurator(Frame owner, Services services, Contract[] contracts, String title,
            boolean allowMultipleContracts) {
        super(owner, "Contract Configurator", true);
        init(services, contracts, title, allowMultipleContracts);
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    /**
     * Helper for constructors.
     */
    private void init(Services services, Contract[] contracts, String title,
            boolean allowMultipleContracts) {
        // create contract panel
        contractPanel = new ContractSelectionPanel(services, allowMultipleContracts);
        contractPanel.setContracts(contracts, title);
        contractPanel.addMouseListener(new MouseAdapter() {
            public void mouseClicked(MouseEvent e) {
                if (e.getClickCount() == 2) {
                    okButton.doClick();
                }
            }
        });
        contractPanel.setMinimumSize(new Dimension(800, 500));
        getContentPane().add(contractPanel);

        // create button panel
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(100, 27);
        buttonPanel
                .setMaximumSize(new Dimension(Integer.MAX_VALUE, (int) buttonDim.getHeight() + 10));
        getContentPane().add(buttonPanel);

        // create "ok" button
        okButton = new JButton("OK");
        okButton.setPreferredSize(buttonDim);
        okButton.setMinimumSize(buttonDim);
        okButton.addActionListener(e -> {
            successful = true;
            setVisible(false);
            dispose();
        });
        buttonPanel.add(okButton);
        getRootPane().setDefaultButton(okButton);

        // create "cancel" button
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(buttonDim);
        cancelButton.setMinimumSize(buttonDim);
        cancelButton.addActionListener(e -> {
            successful = false;
            setVisible(false);
            dispose();
        });
        buttonPanel.add(cancelButton);
        GuiUtilities.attachClickOnEscListener(cancelButton);


        // show
        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
        pack();
        setLocationRelativeTo(getOwner());
        setVisible(true);
    }



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * Tells whether the user clicked "ok".
     */
    public boolean wasSuccessful() {
        return successful;
    }


    /**
     * Returns the selected contract.
     */
    public Contract getContract() {
        return contractPanel.getContract();
    }
}
