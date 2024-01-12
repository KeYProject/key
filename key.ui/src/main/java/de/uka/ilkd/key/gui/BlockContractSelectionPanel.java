/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.AbstractBlockContractBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContractImpl;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * This panel used to select which {@link BlockContract}s to use for an
 * {@link AbstractBlockContractBuiltInRuleApp}.
 */
public class BlockContractSelectionPanel extends AuxiliaryContractSelectionPanel<BlockContract> {

    private static final long serialVersionUID = 1681443715264203991L;

    public BlockContractSelectionPanel(final Services services, final boolean multipleSelection) {
        super(services, multipleSelection);
    }


    /**
     * The static access is used e.g. by the eclipse plugins.
     * <p>
     * Computes the selected {@link BlockContract}.
     * </p>
     * <p>
     * This method is also used by the KeYIDE (Eclipse) to ensure the same behavior.
     * </p>
     *
     * @param services The {@link Services}
     * @param selection The selected contracts.
     * @return The selected {@link BlockContract} or {@code null} if not available.
     */
    public static BlockContract computeBlockContract(Services services,
            List<BlockContract> selection) {
        if (selection.isEmpty()) {
            return null;
        } else if (selection.size() == 1) {
            return selection.get(0);
        } else {
            ImmutableSet<BlockContract> contracts = DefaultImmutableSet.nil();
            for (BlockContract contract : selection) {
                contracts = contracts.add(contract);
            }
            return BlockContractImpl.combine(contracts, services);
        }
    }

    /**
     * <p>
     * Computes the selected {@link BlockContract}.
     * </p>
     * <p>
     * This method is also used by the KeYIDE (Eclipse) to ensure the same behavior.
     * </p>
     *
     * @param services The {@link Services}
     * @param selection The selected contracts.
     * @return The selected {@link BlockContract} or {@code null} if not available.
     */
    @Override
    public BlockContract computeContract(Services services, List<BlockContract> selection) {
        return computeBlockContract(services, selection);
    }
}
