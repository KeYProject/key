/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.event.MouseListener;
import java.util.List;
import javax.swing.*;
import javax.swing.border.TitledBorder;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.BlockContractImpl;
import de.uka.ilkd.key.speclang.LoopContractImpl;

/**
 * This panel used to select which {@code T}(s) to use for a {@link AbstractAuxiliaryContractRule}.
 *
 * @param <T>
 *
 * @see AuxiliaryContractConfigurator
 * @see BlockContractImpl#combine(org.key_project.util.collection.ImmutableSet, Services)
 * @see LoopContractImpl#combine(org.key_project.util.collection.ImmutableSet, Services)
 */
public abstract class AuxiliaryContractSelectionPanel<T extends AuxiliaryContract> extends JPanel {

    private static final long serialVersionUID = 129743953718747490L;

    protected final Services services;
    protected final JList<T> contractList;
    private final TitledBorder border;

    public AuxiliaryContractSelectionPanel(final Services services,
            final boolean multipleSelection) {
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
            private static final long serialVersionUID = 9088858130231994408L;
            private final Font PLAINFONT = getFont().deriveFont(Font.PLAIN);

            public Component getListCellRendererComponent(JList<?> list, Object value, int index,
                    boolean isSelected, boolean cellHasFocus) {
                @SuppressWarnings("unchecked")
                T contract = (T) value;
                Component supComp = super.getListCellRendererComponent(list, value, index,
                    isSelected, cellHasFocus);

                // create label and enclosing panel
                JLabel label = new JLabel();
                label.setText(contract.getHtmlText(serv));
                label.setFont(PLAINFONT);
                FlowLayout lay = new FlowLayout();
                lay.setAlignment(FlowLayout.LEFT);
                JPanel result = new JPanel(lay);
                result.add(label);
                label.setVerticalAlignment(SwingConstants.TOP);

                // set background color
                result.setBackground(supComp.getBackground());

                // set border
                TitledBorder border =
                    new TitledBorder(BorderFactory.createEtchedBorder(), contract.getDisplayName());

                Font borderFont = border.getTitleFont();
                if (borderFont == null) { // MS Windows issues
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
        scrollPane.setViewportView(contractList);
    }

    public synchronized void addMouseListener(final MouseListener ml) {
        contractList.addMouseListener(ml);
    }

    public void setContracts(final T[] contracts, final String title) {
        contractList.setListData(contracts);
        contractList.setSelectedIndex(0);
        if (title != null) {
            border.setTitle(title);
        }
        updateUI();
    }

    public T getContract() {
        final List<T> selection = contractList.getSelectedValuesList();
        return computeContract(services, selection);
    }

    public abstract T computeContract(Services services2, List<T> selection);
}
