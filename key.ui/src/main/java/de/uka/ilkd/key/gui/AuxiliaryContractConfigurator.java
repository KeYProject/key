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
import de.uka.ilkd.key.speclang.AuxiliaryContract;

/**
 * A window to contain a {@link AuxiliaryContractSelectionPanel}.
 *
 * @param <T>
 */
public class AuxiliaryContractConfigurator<T extends AuxiliaryContract> extends JDialog {

    private static final long serialVersionUID = 4882043118399402599L;

    private AuxiliaryContractSelectionPanel<T> contractPanel;
    private JButton okButton;
    private JButton cancelButton;

    private boolean successful = false;

    public AuxiliaryContractConfigurator(final String name,
            final AuxiliaryContractSelectionPanel<T> contractPanel, final JDialog owner,
            final Services services, final T[] contracts, final String title) {
        super(owner, name, true);
        init(services, contractPanel, contracts, title);
    }

    public AuxiliaryContractConfigurator(final String name,
            final AuxiliaryContractSelectionPanel<T> contractPanel, final Frame owner,
            final Services services, final T[] contracts, final String title) {
        super(owner, name, true);
        init(services, contractPanel, contracts, title);
    }

    private void init(final Services services,
            final AuxiliaryContractSelectionPanel<T> contractPanel, final T[] contracts,
            final String title) {
        initContractPanel(services, contractPanel, contracts, title);
        initButtonPanelAndOkAndCancelButtons();
        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
        pack();
        setLocationRelativeTo(getOwner());
        setVisible(true);
    }

    private void initContractPanel(final Services services,
            final AuxiliaryContractSelectionPanel<T> contractPanel, final T[] contracts,
            final String title) {
        this.contractPanel = contractPanel;
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
    }

    private void initButtonPanelAndOkAndCancelButtons() {
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(100, 27);
        buttonPanel
                .setMaximumSize(new Dimension(Integer.MAX_VALUE, (int) buttonDim.getHeight() + 10));
        getContentPane().add(buttonPanel);
        initOkButton(buttonDim, buttonPanel);
        initCancelButton(buttonDim, buttonPanel);
    }

    private void initOkButton(final Dimension dimension, final JPanel container) {
        okButton = new JButton("OK");
        okButton.setPreferredSize(dimension);
        okButton.setMinimumSize(dimension);
        okButton.addActionListener(event -> {
            successful = true;
            setVisible(false);
            dispose();
        });
        container.add(okButton);
        getRootPane().setDefaultButton(okButton);
    }

    private void initCancelButton(final Dimension dimension, final JPanel container) {
        cancelButton = new JButton("Cancel");
        cancelButton.setPreferredSize(dimension);
        cancelButton.setMinimumSize(dimension);
        cancelButton.addActionListener(event -> {
            successful = false;
            setVisible(false);
            dispose();
        });
        container.add(cancelButton);
        GuiUtilities.attachClickOnEscListener(cancelButton);
    }

    /**
     * Tells whether the user clicked "OK".
     */
    public boolean wasSuccessful() {
        return successful;
    }

    /**
     * Returns the selected contract.
     */
    public T getContract() {
        return contractPanel.getContract();
    }

}
