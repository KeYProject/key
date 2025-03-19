/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.BlockContract;

import org.key_project.util.collection.ImmutableList;

/**
 * Application of {@link BlockContractExternalRule}.
 *
 * @author lanzinger
 */
public class BlockContractExternalBuiltInRuleApp extends AbstractBlockContractBuiltInRuleApp {

    /**
     *
     * @param rule the rule being applied.
     * @param occurrence the position at which the rule is applied.
     */
    public BlockContractExternalBuiltInRuleApp(final BuiltInRule rule,
            final PosInOccurrence occurrence) {
        this(rule, occurrence, null, null, null, null);
    }

    /**
     *
     * @param rule the rule being applied.
     * @param occurrence the position at which the rule is applied.
     * @param ifInstantiations if instantiations.
     * @param statement the statement which the applied contract belongs to.
     * @param contract the contract being applied.
     * @param heaps the heap context.
     */
    public BlockContractExternalBuiltInRuleApp(final BuiltInRule rule,
            final PosInOccurrence occurrence, final ImmutableList<PosInOccurrence> ifInstantiations,
            final JavaStatement statement, final BlockContract contract,
            final List<LocationVariable> heaps) {
        super(rule, occurrence, ifInstantiations);
        assert rule != null;
        assert rule instanceof BlockContractExternalRule;
        assert occurrence != null;
        setStatement(statement);
        this.contract = contract;
        this.heaps = heaps;
    }

    @Override
    public BlockContractExternalBuiltInRuleApp replacePos(final PosInOccurrence newOccurrence) {
        return new BlockContractExternalBuiltInRuleApp(builtInRule, newOccurrence, ifInsts,
            getStatement(), contract, heaps);
    }

    @Override
    public BlockContractExternalBuiltInRuleApp setIfInsts(
            final ImmutableList<PosInOccurrence> ifInstantiations) {
        setMutable(ifInstantiations);
        return this;
    }

    @Override
    public BlockContractExternalBuiltInRuleApp tryToInstantiate(final Goal goal) {
        return (BlockContractExternalBuiltInRuleApp) super.tryToInstantiate(goal,
            BlockContractExternalRule.INSTANCE);
    }
}
