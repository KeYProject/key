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

import java.util.List;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.AbstractBlockContractBuiltInRuleApp;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.SimpleBlockContract;

/**
 * This panel used to select which {@link BlockContract}s to use for an
 * {@link AbstractBlockContractBuiltInRuleApp}.
 */
public class BlockContractSelectionPanel extends BlockSpecificationElementSelectionPanel<BlockContract> {

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
     * @param services The {@link Services}
     * @param selection The selected contracts.
     * @return The selected {@link BlockContract} or {@code null} if not available.
     */
    public static BlockContract computeBlockContract(
            Services services, List<BlockContract> selection) {
        if (selection.isEmpty()) {
            return null;
        }
        else if (selection.size() == 1) {
            return selection.get(0);
        }
        else {
            ImmutableSet<BlockContract> contracts = DefaultImmutableSet.nil();
            for (BlockContract contract : selection) {
                contracts = contracts.add(contract);
            }
            return SimpleBlockContract.combine(contracts, services);
        }        
    }

    /**
     * <p>
     * Computes the selected {@link BlockContract}.
     * </p>
     * <p>
     * This method is also used by the KeYIDE (Eclipse) to ensure the same behavior.
     * </p>
     * @param services The {@link Services}
     * @param selection The selected contracts.
     * @return The selected {@link BlockContract} or {@code null} if not available.
     */
    @Override
    public BlockContract computeContract(
            Services services, List<BlockContract> selection) {
      return computeBlockContract(services, selection);
    }
}