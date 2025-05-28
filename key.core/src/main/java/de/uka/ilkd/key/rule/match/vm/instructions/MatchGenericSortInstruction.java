/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

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

public class MatchGenericSortInstruction implements MatchInstruction {

    private final GenericSort genericSortOfOp;

    public MatchGenericSortInstruction(GenericSort sort) {
        this.genericSortOfOp = sort;
    }

    /**
     * matches the depending sort of this instructions sort depending function against the given
     * sort. If a match is possible the resulting match conditions are returned otherwise
     * {@code null} is returned.
     *
     * @param dependingSortToMatch the depending {@link Sort} of the concrete function to be matched
     * @param matchConditions the {@link MatchResultInfo} accumulated so far
     * @return <code>null</code> if failed the resulting match conditions otherwise the resulting
     *         {@link MatchResultInfo}
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
        return matchSorts(((QualifierWrapper<Sort>) actualElement).getQualifier(), mc, services);
    }

}
