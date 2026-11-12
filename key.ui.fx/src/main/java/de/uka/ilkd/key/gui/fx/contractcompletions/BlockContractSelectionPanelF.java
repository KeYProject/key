/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.contractcompletions;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.BlockContractImpl;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * contractcompletions (P2b): JavaFX port of the Swing {@code BlockContractSelectionPanel}
 * (BlockContractSelectionPanel.java, 74 lines) — the auxiliary-contract panel for block
 * contracts; several selected contracts are combined via {@code BlockContractImpl.combine}.
 */
public class BlockContractSelectionPanelF extends AuxiliaryContractSelectionPanelF<BlockContract> {

    public BlockContractSelectionPanelF(final Services services, final boolean multipleSelection) {
        super(services, multipleSelection);
    }

    /** Swing {@code computeBlockContract}. */
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

    @Override
    public BlockContract computeContract(Services services, List<BlockContract> selection) {
        return computeBlockContract(services, selection);
    }
}
