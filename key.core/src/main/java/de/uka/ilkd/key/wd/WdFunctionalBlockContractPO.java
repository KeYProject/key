/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.macros.WellDefinednessMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders;
import de.uka.ilkd.key.speclang.AuxiliaryContract;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.FunctionalBlockContract;

import org.key_project.logic.op.Function;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (8/3/25)
 */
public class WdFunctionalBlockContractPO extends FunctionalBlockContractPO {
    /**
     * @param initConfig the initial proof configuration.
     * @param contract the contract from which this PO is generated.
     */
    public WdFunctionalBlockContractPO(InitConfig initConfig, FunctionalBlockContract contract) {
        super(initConfig, contract);
    }

    /**
     * @param validity the validity formula.
     * @param updates the updates.
     * @param heaps the heaps.
     * @param anonOutHeaps the heaps used in the anonOut update.
     * @param localInVariables the free local variables in the block.
     * @param localOutVariables the free local variables modifiable by the block.
     * @param bc the contract being applied.
     * @param configurator a goal configurator
     * @param services services.
     * @param tb a term builder.
     * @return the conjunction of the well-definedness formula and the validity formula.
     */
    protected JTerm addWdToValidityTerm(JTerm validity, final JTerm[] updates,
            final List<LocationVariable> heaps, Map<LocationVariable, Function> anonOutHeaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ImmutableSet<LocationVariable> localOutVariables, final BlockContract bc,
            final AuxiliaryContractBuilders.GoalsConfigurator configurator,
            final Services services, final TermBuilder tb) {
        if (WellDefinednessCheck.isOn()) {
            final JTerm wdUpdate = services.getTermBuilder().parallel(updates[1], updates[2]);

            JTerm localAnonUpdate = createLocalAnonUpdate(localOutVariables, services, tb);

            if (localAnonUpdate == null) {
                localAnonUpdate = tb.skip();
            }

            JTerm wellDefinedness = setUpWdGoal(null, bc, wdUpdate, localAnonUpdate,
                heaps.getFirst(), anonOutHeaps.get(heaps.getFirst()), localInVariables,
                services, null, null);

            validity = tb.and(wellDefinedness, validity);
        }
        return validity;
    }

    @Override
    protected JTerm setUpValidityTerm(List<LocationVariable> heaps,
            Map<LocationVariable, Function> anonHeaps, Map<LocationVariable, Function> anonOutHeaps,
            ImmutableSet<LocationVariable> localInVariables,
            ImmutableSet<LocationVariable> localOutVariables, ProgramVariable exceptionParameter,
            JTerm[] assumptions, JTerm[] postconditions, JTerm[] updates, BlockContract bc,
            AuxiliaryContractBuilders.ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            AuxiliaryContractBuilders.GoalsConfigurator configurator, Services services,
            TermBuilder tb) {
        var validity = super.setUpValidityTerm(heaps, anonHeaps, anonOutHeaps, localInVariables,
            localOutVariables, exceptionParameter, assumptions, postconditions, updates, bc,
            conditionsAndClausesBuilder, configurator, services, tb);
        return addWdToValidityTerm(validity, updates, heaps, anonOutHeaps, localInVariables,
            localOutVariables, bc, configurator, services, tb);
    }

    /**
     * @param goal If this is not {@code null}, the returned formula is added to this goal.
     * @param contract the contract being applied.
     * @param update the update.
     * @param anonUpdate the anonymization update.
     * @param heap the heap.
     * @param anonHeap the anonymization heap.
     * @param localIns all free local variables in the block.
     * @param variables
     * @param occurrence
     * @return the well-definedness formula.
     */
    public static JTerm setUpWdGoal(final @Nullable Goal goal, final BlockContract contract,
            final JTerm update,
            final JTerm anonUpdate, final LocationVariable heap, final Function anonHeap,
            final ImmutableSet<LocationVariable> localIns,
            Services services,
            AuxiliaryContract.Variables variables, PosInOccurrence occurrence) {
        // FIXME: Handling of \old-references needs to be investigated,
        // however only completeness is lost, soundness is guaranteed
        final BlockWellDefinedness bwd =
            new BlockWellDefinedness(contract, variables, localIns, services);
        services.getSpecificationRepository().addWdStatement(bwd);
        final LocationVariable heapAtPre = variables.remembranceHeaps.get(heap);
        final JTerm anon = anonHeap != null ? services.getTermBuilder().func(anonHeap) : null;
        final SequentFormula wdBlock = bwd.generateSequent(
            variables.self, variables.exception,
            variables.result, heap, heapAtPre, anon, localIns, update, anonUpdate, services);

        if (goal != null) {
            goal.setBranchLabel(WellDefinednessMacro.WD_BRANCH);
            goal.changeFormula(wdBlock, occurrence);
        }

        return (JTerm) wdBlock.formula();
    }
}
