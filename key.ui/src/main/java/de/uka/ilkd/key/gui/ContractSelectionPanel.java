/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseListener;
import java.util.*;
import java.util.List;
import javax.swing.*;
import javax.swing.border.TitledBorder;
import javax.swing.event.ListSelectionListener;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.LinkedHashMap;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;


/**
 * A panel for selecting contracts.
 */
public class ContractSelectionPanel extends JPanel {

    /**
     *
     */
    private static final long serialVersionUID = 1681223715264203991L;

    private static final Map<Class<?>, Integer> CONTRACT_TYPE_ORDER = new LinkedHashMap<>();
    static {
        CONTRACT_TYPE_ORDER.put(FunctionalOperationContractImpl.class, 0);
        CONTRACT_TYPE_ORDER.put(InformationFlowContractImpl.class, 1);
        CONTRACT_TYPE_ORDER.put(DependencyContractImpl.class, 2);
        CONTRACT_TYPE_ORDER.put(FunctionalBlockContract.class, 3);
        CONTRACT_TYPE_ORDER.put(FunctionalLoopContract.class, 4);
    }

    private final Services services;
    private final JList<Contract> contractList;
    private final TitledBorder border;
    private Contract[] contracts = new Contract[0];

    /**
     * Whether or not an auxiliary contract should be grayed out if is has not been applied in a
     * proof for a non-auxiliary contract.
     *
     * @see Contract#isAuxiliary()
     */
    private boolean grayOutAuxiliaryContracts = false;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    /**
     * Creates a contract selection panel containing the specified contracts.
     */
    public ContractSelectionPanel(Services services, boolean multipleSelection) {
        setLayout(new BoxLayout(this, BoxLayout.Y_AXIS));
        this.services = services;

        // create scroll pane
        JScrollPane scrollPane = new JScrollPane();
        border = new TitledBorder("Contracts");
        scrollPane.setBorder(border);
        Dimension scrollPaneDim = new Dimension(700, 500);
        scrollPane.setPreferredSize(scrollPaneDim);
        scrollPane.setMinimumSize(scrollPaneDim);
        add(scrollPane);

        // create contract list
        contractList = new JList<>();
        contractList
                .setSelectionMode(multipleSelection ? ListSelectionModel.MULTIPLE_INTERVAL_SELECTION
                        : ListSelectionModel.SINGLE_SELECTION);
        contractList.addListSelectionListener(e -> {
            if (contractList.isSelectionEmpty()) {
                contractList.setSelectedIndex(e.getFirstIndex());
            }
        });
        final Services serv = services;
        contractList.setCellRenderer(new DefaultListCellRenderer() {
            /**
             *
             */
            private static final long serialVersionUID = 9066658130231994408L;
            private final Font PLAINFONT = getFont().deriveFont(Font.PLAIN);

            public Component getListCellRendererComponent(JList<?> list, Object value, int index,
                    boolean isSelected, boolean cellHasFocus) {
                assert value != null;
                Contract contract = (Contract) value;
                Component supComp = super.getListCellRendererComponent(list, value, index,
                    isSelected, cellHasFocus);

                // Find all contracts that were applied in a proof for a non-auxiliary contract.
                Set<Contract> appliedContracts = new HashSet<>();
                Set<Contract> consideredContracts = new HashSet<>();

                for (Contract c : contracts) {
                    if (c.isAuxiliary()) {
                        continue;
                    }

                    consideredContracts.add(c);
                    Proof p = getClosedProof(c);

                    if (p != null) {
                        for (Contract used : p.mgt().getUsedContracts()) {
                            appliedContracts.add(used);
                        }
                    }
                }

                final int iterations = contracts.length - consideredContracts.size();
                for (int i = 0; i < iterations; ++i) {
                    for (Contract c : contracts) {
                        if (consideredContracts.contains(c) || !appliedContracts.contains(c)) {
                            continue;
                        }

                        consideredContracts.add(c);
                        Proof p = getClosedProof(c);

                        if (p != null) {
                            for (Contract used : p.mgt().getUsedContracts()) {
                                appliedContracts.add(used);
                            }
                        }
                    }
                }

                // create label and enclosing panel
                JLabel label = new JLabel();
                label.setText(contract.getHTMLText(serv));
                label.setFont(PLAINFONT);
                FlowLayout lay = new FlowLayout();
                lay.setAlignment(FlowLayout.LEFT);
                JPanel result = new JPanel(lay);
                result.add(label);
                label.setVerticalAlignment(SwingConstants.TOP);

                result.setBackground(supComp.getBackground());

                // set border and text color
                // (if applicable, gray out unnecessary auxiliary contracts)
                TitledBorder border;
                Font borderFont;
                if (grayOutAuxiliaryContracts && contract.isAuxiliary()
                        && !appliedContracts.contains(contract)) {
                    label.setForeground(Color.GRAY);

                    border = new TitledBorder(BorderFactory.createEtchedBorder(),
                        contract.getDisplayName(), TitledBorder.LEADING,
                        TitledBorder.DEFAULT_POSITION, null, Color.GRAY);

                    borderFont = border.getTitleFont();
                    if (borderFont == null) { // MS Windows issues
                        borderFont = result.getFont();
                        if (borderFont == null) {
                            borderFont = PLAINFONT;
                        }
                    }
                } else {
                    border = new TitledBorder(BorderFactory.createEtchedBorder(),
                        contract.getDisplayName());

                    borderFont = border.getTitleFont();
                    if (borderFont == null) { // MS Windows issues
                        borderFont = result.getFont();
                        if (borderFont == null) {
                            borderFont = PLAINFONT;
                        }
                    }
                }
                border.setTitleFont(borderFont.deriveFont(Font.BOLD));
                result.setBorder(border);

                return result;
            }
        });
        scrollPane.setViewportView(contractList);
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------

    private Proof getClosedProof(Contract c) {
        ImmutableSet<Proof> proofs = services.getSpecificationRepository().getProofs(c);

        for (Proof proof : proofs) {
            if (proof.mgt().getStatus().getProofClosed()) {
                return proof;
            }
        }

        return null;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public synchronized void addMouseListener(MouseListener ml) {
        contractList.addMouseListener(ml);
    }


    public void addListSelectionListener(ListSelectionListener lsl) {
        contractList.addListSelectionListener(lsl);
    }

    /**
     *
     * @param grayOutAuxiliaryContracts whether or not an auxiliary contract should be grayed out if
     *        it has not been applied in a proof for a non-auxiliary contract.
     *
     * @see Contract#isAuxiliary()
     */
    public void setGrayOutAuxiliaryContracts(boolean grayOutAuxiliaryContracts) {
        this.grayOutAuxiliaryContracts = grayOutAuxiliaryContracts;
    }


    public void setContracts(Contract[] contracts, String title) {
        if (contracts == null || contracts.length == 0) {
            this.contracts = new Contract[0];
            contractList.setListData(this.contracts);
            updateUI();
            return;
        }

        // sort contracts by contract type, then by name
        Arrays.sort(contracts, (c1, c2) -> {
            Integer o1 = CONTRACT_TYPE_ORDER.get(c1.getClass());
            Integer o2 = CONTRACT_TYPE_ORDER.get(c2.getClass());
            int res = 0;

            if (o1 != null && o2 != null) {
                res = o1 - o2;
            } else if (o1 != null) {
                return -1;
            } else if (o2 != null) {
                return 1;
            }

            if (res != 0) {
                return res;
            }

            res = c1.getDisplayName().compareTo(c2.getDisplayName());
            if (res == 0) {
                return c1.id() - c2.id();
            }
            return res;
        });

        this.contracts = contracts;
        contractList.setListData(contracts);
        contractList.setSelectedIndex(0);
        if (title != null) {
            border.setTitle(title);
        }
        updateUI();
    }


    public void setContracts(ImmutableSet<Contract> contracts, String title) {
        setContracts(contracts.toArray(new Contract[contracts.size()]), title);
    }

    /**
     * Selects the given contract in the list.
     *
     * @param contract The {@link Contract}
     */
    public void selectContract(Contract contract) {
        contractList.setSelectedValue(contract, true);
    }

    public Contract getContract() {
        final List<Contract> selection = contractList.getSelectedValuesList();
        return computeContract(services, selection);
    }

    /**
     * <p>
     * Computes the selected {@link Contract}.
     * </p>
     * <p>
     * This method is also used by the KeYIDE (Eclipse) to ensure the same behavior.
     * </p>
     *
     * @param services The {@link Services}
     * @param selection The selected contracts.
     * @return The selected {@link Contract} or {@code null} if not available.
     */
    public static Contract computeContract(Services services, List<Contract> selection) {
        if (selection.isEmpty()) {
            return null;
        } else if (selection.size() == 1) {
            return selection.get(0);
        } else {
            ImmutableSet<FunctionalOperationContract> contracts =
                DefaultImmutableSet.nil();
            for (Contract contract : selection) {
                if (contract instanceof FunctionalOperationContract) {
                    contracts = contracts.add((FunctionalOperationContract) contract);
                } else {
                    throw new IllegalStateException(
                        "Don't know how to combine contracts of kind " + contract.getClass() + "\n"
                            + "Contract:\n" + contract.getPlainText(services));
                }
            }
            return services.getSpecificationRepository().combineOperationContracts(contracts);
        }
    }
}
