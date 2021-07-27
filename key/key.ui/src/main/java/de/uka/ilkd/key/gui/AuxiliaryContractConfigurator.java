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
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.KeyEvent;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import javax.swing.BoxLayout;
import javax.swing.JButton;
import javax.swing.JComponent;
import javax.swing.JDialog;
import javax.swing.JPanel;
import javax.swing.KeyStroke;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.AuxiliaryContract;

/**
 * A window to contain a {@link AuxiliaryContractSelectionPanel}.
 *
 * @param <T>
 */
public class AuxiliaryContractConfigurator<T extends AuxiliaryContract>
        extends JDialog {

    private static final long serialVersionUID = 4882043118399402599L;

    private AuxiliaryContractSelectionPanel<T> contractPanel;
    private JButton okButton;
    private JButton cancelButton;

    private boolean successful = false;

    public AuxiliaryContractConfigurator(final String name,
                                     final AuxiliaryContractSelectionPanel<T> contractPanel,
                                     final JDialog owner,
                                     final Services services,
                                     final T[] contracts,
                                     final String title) {
        super(owner, name, true);
        init(services, contractPanel, contracts, title);
    }

    public AuxiliaryContractConfigurator(final String name,
                                     final AuxiliaryContractSelectionPanel<T> contractPanel,
                                     final Frame owner,
                                     final Services services,
                                     final T[] contracts,
                                     final String title) {
        super(owner, name, true);
        init(services, contractPanel, contracts, title);
    }

    private void init(final Services services,
            final AuxiliaryContractSelectionPanel<T> contractPanel,
                      final T[] contracts,
                      final String title) {
        initContractPanel(services, contractPanel, contracts, title);
        initButtonPanelAndOkayAndCancelButtons();
        getContentPane().setLayout(new BoxLayout(getContentPane(), BoxLayout.Y_AXIS));
        pack();
        setLocation(70, 70);
        setVisible(true);
    }

    private void initContractPanel(final Services services,
                                   final AuxiliaryContractSelectionPanel<T> contractPanel,
                                   final T[] contracts,
                                   final String title) {
        this.contractPanel = contractPanel;
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

    private void initButtonPanelAndOkayAndCancelButtons() {
        JPanel buttonPanel = new JPanel();
        buttonPanel.setLayout(new FlowLayout(FlowLayout.RIGHT, 5, 5));
        Dimension buttonDim = new Dimension(100, 27);
        buttonPanel.setMaximumSize(new Dimension(Integer.MAX_VALUE, (int) buttonDim.getHeight() + 10));
        getContentPane().add(buttonPanel);
        initOkayButton(buttonDim, buttonPanel);
        initCancelButton(buttonDim, buttonPanel);
    }

    private void initOkayButton(final Dimension dimension, final JPanel container) {
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

    private void initCancelButton(final Dimension dimension, final JPanel container) {
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
    public T getContract() {
        return contractPanel.getContract();
    }

}