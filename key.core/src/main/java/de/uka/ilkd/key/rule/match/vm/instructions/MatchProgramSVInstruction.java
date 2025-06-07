/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.IllegalInstantiationException;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class MatchProgramSVInstruction extends MatchSchemaVariableInstruction {

    private static final Logger LOGGER = LoggerFactory.getLogger(MatchProgramSVInstruction.class);

    public MatchProgramSVInstruction(ProgramSV sv) {
        super(sv);
    }

    /**
     * tries to add the pair <tt>(this,pe)</tt> to the match conditions. If possible the resulting
     * match conditions are returned, otherwise <tt>null</tt>. Such an addition can fail, e.g. if
     * already a pair <tt>(this,x)</tt> exists where <tt>x!=pe</tt>
     */
    protected MatchResultInfo addInstantiation(ProgramElement pe, MatchResultInfo matchCond,
            LogicServices services) {

        final SVInstantiations instantiations = (SVInstantiations) matchCond.getInstantiations();
        final Object inMap = instantiations.getInstantiation(op);

        if (inMap == null) {
            try {
                return matchCond.setInstantiations(instantiations.add(op, pe, services));
            } catch (IllegalInstantiationException e) {
                LOGGER.debug("Exception thrown by class Taclet at setInstantiations");
            }
        } else {
            Object peForCompare = pe;
            if (inMap instanceof JTerm) {
                try {
                    peForCompare =
                        ((Services) services).getTypeConverter().convertToLogicElement(pe,
                            instantiations.getExecutionContext());
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
    public MatchResultInfo match(ProgramElement instantiationCandidate,
            MatchResultInfo matchCond,
            LogicServices services) {
        final ProgramSVSort svSort = (ProgramSVSort) op.sort();

        final SVInstantiations instantiations = (SVInstantiations) matchCond.getInstantiations();
        if (svSort.canStandFor(instantiationCandidate,
            instantiations.getExecutionContext(), (Services) services)) {
            return addInstantiation(instantiationCandidate, matchCond, services);
        }

        return null;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo mc,
            LogicServices services) {
        MatchResultInfo result = null;
        if (actualElement instanceof ProgramElement programElement) {
            result = match(programElement, mc, services);
        } else if (actualElement instanceof JTerm term) {
            final ProgramSVSort svSort = (ProgramSVSort) op.sort();
            if (svSort.canStandFor(term)) {
                return addInstantiation(term, mc, services);
            }
        }
        return result;
    }
}
