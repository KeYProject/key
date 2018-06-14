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

package de.uka.ilkd.key.rule;

import java.util.List;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.BlockContract;

/**
 * Application of {@link BlockContractInternalRule}.
 *
 * @author wacker, lanzinger
 */
public class BlockContractInternalBuiltInRuleApp extends AbstractBlockContractBuiltInRuleApp {

    /**
     *
     * @param rule
     *            the rule being applied.
     * @param occurrence
     *            the position at which the rule is applied.
     */
    public BlockContractInternalBuiltInRuleApp(final BuiltInRule rule,
            final PosInOccurrence occurrence) {
        this(rule, occurrence, null, null, null, null);
    }

    /**
     *
     * @param rule
     *            the rule being applied.
     * @param occurrence
     *            the position at which the rule is applied.
     * @param ifInstantiations
     *            if instantiations.
     * @param block
     *            the block which the applied contract belongs to.
     * @param contract
     *            the contract being applied.
     * @param heaps
     *            the heap context.
     */
    public BlockContractInternalBuiltInRuleApp(final BuiltInRule rule,
            final PosInOccurrence occurrence, final ImmutableList<PosInOccurrence> ifInstantiations,
            final StatementBlock block, final BlockContract contract,
            final List<LocationVariable> heaps) {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert rule instanceof BlockContractInternalRule;
        assert occurrence != null;
        this.block = block;
        this.contract = contract;
        this.heaps = heaps;
    }

    @Override
    public BlockContractInternalBuiltInRuleApp replacePos(final PosInOccurrence newOccurrence) {
        return new BlockContractInternalBuiltInRuleApp(builtInRule, newOccurrence, ifInsts, block,
                contract, heaps);
    }

    @Override
    public BlockContractInternalBuiltInRuleApp setIfInsts(
            final ImmutableList<PosInOccurrence> ifInstantiations) {
        setMutable(ifInstantiations);
        return this;
    }

    @Override
    public BlockContractInternalBuiltInRuleApp tryToInstantiate(final Goal goal) {

        return (BlockContractInternalBuiltInRuleApp) super.tryToInstantiate(goal,
                BlockContractInternalRule.INSTANCE);
    }
}
