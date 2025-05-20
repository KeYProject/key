/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class MatchProgramSVInstruction extends MatchSchemaVariableInstruction<ProgramSV>
        implements MatchOperatorInstruction {

    private static final Logger LOGGER = LoggerFactory.getLogger(MatchProgramSVInstruction.class);

    public MatchProgramSVInstruction(@NonNull ProgramSV sv) {
        super(sv);
    }


    /**
     * tries to add the pair <tt>(this,pe)</tt> to the match conditions. If possible the resulting
     * match conditions are returned, otherwise <tt>null</tt>. Such an addition can fail, e.g. if
     * already a pair <tt>(this,x)</tt> exists where <tt>x!=pe</tt>
     */
    protected @Nullable MatchConditions addInstantiation(@NonNull ProgramElement pe,
            @NonNull MatchConditions matchCond,
            @NonNull Services services) {

        final SVInstantiations instantiations = matchCond.getInstantiations();
        final Object inMap = instantiations.getInstantiation(op);

        if (inMap == null) {
            try {
                return matchCond.setInstantiations(instantiations.add(op, pe, services));
            } catch (IllegalInstantiationException e) {
                LOGGER.debug("Exception thrown by class Taclet at setInstantiations");
            }
        } else {
            Object peForCompare = pe;
            if (inMap instanceof Term) {
                try {
                    peForCompare = services.getTypeConverter().convertToLogicElement(pe,
                        matchCond.getInstantiations().getExecutionContext());
                } catch (RuntimeException re) {
                    return null;
                }
            }
            if (inMap.equals(peForCompare)) {
                return matchCond;
            }
        }
        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchConditions match(Operator instantiationCandidate,
            @NonNull MatchConditions matchConditions,
            @NonNull Services services) {
        if (instantiationCandidate instanceof ProgramElement) {
            return match((ProgramElement) instantiationCandidate, matchConditions, services);
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchConditions match(@NonNull Term instantiationCandidate,
            @NonNull MatchConditions matchCond,
            @NonNull Services services) {
        final ProgramSVSort svSort = (ProgramSVSort) op.sort();

        if (svSort.canStandFor(instantiationCandidate)) {
            return addInstantiation(instantiationCandidate, matchCond, services);
        }

        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchConditions match(@NonNull ProgramElement instantiationCandidate,
            @NonNull MatchConditions matchCond,
            @NonNull Services services) {
        final ProgramSVSort svSort = (ProgramSVSort) op.sort();

        if (svSort.canStandFor(instantiationCandidate,
            matchCond.getInstantiations().getExecutionContext(), services)) {
            return addInstantiation(instantiationCandidate, matchCond, services);
        }

        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable MatchConditions match(@NonNull TermNavigator termPosition,
            @NonNull MatchConditions mc,
            @NonNull Services services) {
        MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;
    }
}
