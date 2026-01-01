/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BlockContractInternalRule;
import de.uka.ilkd.key.speclang.BlockContract;

import org.key_project.logic.op.Function;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import static de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;

/**
 * @author Alexander Weigl
 * @version 1 (7/27/25)
 */
public class WdBlockContractInternalRule extends BlockContractInternalRule {
    @Override
    protected ImmutableList<Goal> splitIntoGoals(Goal goal, BlockContract contract,
            List<LocationVariable> heaps,
            ImmutableSet<LocationVariable> localInVariables,
            Map<LocationVariable, Function> anonymisationHeaps,
            JTerm contextUpdate, JTerm remembranceUpdate,
            ImmutableSet<LocationVariable> localOutVariables,
            GoalsConfigurator configurator, Services services) {
        LocationVariable heap = heaps.getFirst();
        var result = goal.split(4);
        JTerm localAnonUpdate = createLocalAnonUpdate(localOutVariables, services);
        JTerm wdUpdate = services.getTermBuilder().parallel(contextUpdate, remembranceUpdate);
        WdFunctionalBlockContractPO.setUpWdGoal(
            result.get(3), contract, wdUpdate,
            localAnonUpdate, heap, anonymisationHeaps.get(heap), localInVariables,
            configurator.services,
            configurator.variables,
            configurator.occurrence);
        return result;
    }
}
