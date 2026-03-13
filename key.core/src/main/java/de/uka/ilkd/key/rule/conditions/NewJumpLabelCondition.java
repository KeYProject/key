/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.visitor.LabelCollector;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

/**
 * This variable condition ensures that no other label of the same name exists in the context
 * program or one of the schemavariable instantiations.
 */
public final class NewJumpLabelCondition implements VariableCondition {

    private final ProgramSV labelSV;

    public NewJumpLabelCondition(SchemaVariable sv) {
        if (!(sv instanceof ProgramSV psv) || psv.sort() != ProgramSVSort.LABEL) {
            throw new IllegalArgumentException(
                "The new jump label " + "variable condition, must be parameterised with a "
                    + "program schemavariable of sort LABEL.");
        }

        labelSV = psv;
    }

    @Override
    public MatchConditions check(SchemaVariable var,
            SyntaxElement instCandidate,
            MatchResultInfo matchCond,
            LogicServices services) {
        SVInstantiations instantiations = (SVInstantiations) matchCond.getInstantiations();
        if (var != labelSV && instantiations.isInstantiated(labelSV)) {
            var = labelSV;
            instCandidate = (SyntaxElement) instantiations.getInstantiation(labelSV);
        }

        if (var == labelSV) {
            if (!(instCandidate instanceof Label)) {
                return null;
            }
            final List<ProgramElement> programs = collect(instantiations);
            programs.add(instantiations.getContextInstantiation().program());
            if (!isUnique((Label) instCandidate, programs, services)) {
                return null;
            }
        }
        return (MatchConditions) matchCond;
    }

    private List<ProgramElement> collect(SVInstantiations inst) {
        final List<ProgramElement> result = new LinkedList<>();
        for (final var entry : inst.getInstantiationMap()) {
            if (entry.key() != labelSV && entry.value() != null
                    && entry.value().getInstantiation() instanceof ProgramElement) {
                result.add((ProgramElement) entry.value().getInstantiation());
            }
        }
        return result;
    }

    private boolean isUnique(Label label, List<ProgramElement> programs, LogicServices services) {
        final Services javaServices = (Services) services;
        for (final ProgramElement pe : programs) {
            final LabelCollector lc = new LabelCollector(pe, javaServices);
            lc.start();
            if (lc.contains(label)) {
                return false;
            }
        }
        return true;
    }


    @Override
    public String toString() {
        return "\\newLabel (" + labelSV + ")";
    }
}
