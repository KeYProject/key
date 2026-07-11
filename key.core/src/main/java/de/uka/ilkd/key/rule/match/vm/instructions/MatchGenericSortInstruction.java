/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.logic.GenericArgument;
import de.uka.ilkd.key.logic.op.QualifierWrapper;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.SortException;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

/**
 * Matches a generic sort of the pattern against the concrete sort found in the source — the sort
 * of a parametric function's {@link GenericArgument} or of a {@link QualifierWrapper} — by
 * recording an identity {@link GenericSortCondition} in the instantiations: the generic sort must
 * be (or already have been) instantiated with exactly that concrete sort.
 */
public class MatchGenericSortInstruction implements MatchInstruction {

    private final GenericSort genericSortOfOp;

    public MatchGenericSortInstruction(GenericSort sort) {
        this.genericSortOfOp = sort;
    }

    /**
     * Matches this instruction's generic sort against the given concrete sort by adding the
     * corresponding identity condition. If that is consistent with the instantiations so far the
     * resulting match conditions are returned, otherwise {@code null}.
     *
     * @param dependingSortToMatch the concrete {@link Sort} found in the source
     * @param matchConditions the {@link MatchResultInfo} accumulated so far
     * @return the resulting {@link MatchResultInfo}, or {@code null} on failure
     */
    private MatchResultInfo matchSorts(Sort dependingSortToMatch, MatchResultInfo matchConditions,
            LogicServices services) {
        // This restriction has been dropped for free generic sorts to prove taclets correct
        // assert !(s2 instanceof GenericSort)
        // : "Sort s2 is not allowed to be of type generic.";
        MatchResultInfo result;
        final GenericSortCondition c =
            GenericSortCondition.createIdentityCondition(genericSortOfOp, dependingSortToMatch);
        try {
            final SVInstantiations instantiations =
                (SVInstantiations) matchConditions.getInstantiations();
            return matchConditions.setInstantiations(instantiations.add(c, services));
        } catch (SortException e) {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchResultInfo match(SyntaxElement actualElement, MatchResultInfo mc,
            LogicServices services) {
        if (actualElement instanceof GenericArgument(Sort sort)) {
            return matchSorts(sort, mc, services);
        }
        if (actualElement instanceof QualifierWrapper<?> w
                && w.getQualifier() instanceof Sort sort) {
            return matchSorts(sort, mc, services);
        }
        return null;
    }

}
