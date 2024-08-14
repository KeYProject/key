/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.LogicVariable;
import org.key_project.rusty.logic.op.sv.VariableSV;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.util.collection.ImmutableArray;

/**
 * This instructions matches the variable below a binder (e.g. a quantifier).
 */
public class BindVariablesInstruction implements MatchInstruction {
    private final VariableBinderSubinstruction[] boundVarBinders;

    public BindVariablesInstruction(ImmutableArray<? extends QuantifiableVariable> boundVars) {
        boundVarBinders = new VariableBinderSubinstruction[boundVars.size()];
        int i = 0;
        for (QuantifiableVariable boundVar : boundVars) {
            if (boundVar instanceof LogicVariable lv) {
                boundVarBinders[i] = new LogicVariableBinder(lv);
            } else {
                boundVarBinders[i] = new VariableSVBinder((VariableSV) boundVar);
            }
            i++;
        }
    }


    private interface VariableBinderSubinstruction {
        MatchConditions match(LogicVariable instantiationCandidate,
                MatchConditions matchCond, Services services);
    }

    private record LogicVariableBinder(LogicVariable templateVar) implements VariableBinderSubinstruction {

    /**
     * a match between two logic variables is possible if they have been assigned they are same
     * or have been assigned to the same abstract name and the sorts are equal.
     */
    public MatchConditions match(LogicVariable instantiationCandidate,
            MatchConditions matchCond, Services services) {
        if (templateVar != instantiationCandidate) {
            if (instantiationCandidate.sort() != templateVar.sort()) {
                matchCond = null;
            }
        }
        return matchCond;
    }
}


private static class VariableSVBinder extends MatchSchemaVariableInstruction<VariableSV>
        implements VariableBinderSubinstruction {

    public VariableSVBinder(VariableSV templateVar) {
        super(templateVar);
    }

    public MatchConditions match(LogicVariable instantiationCandidate,
            MatchConditions matchCond, Services services) {
        final Object foundMapping = matchCond.getInstantiations().getInstantiation(op);
        if (foundMapping == null) {
            final Term substTerm = services.getTermBuilder().var(instantiationCandidate);
            matchCond = addInstantiation(substTerm, matchCond, services);
        } else if (((Term) foundMapping).op() != instantiationCandidate) {
            matchCond = null;
        }
        return matchCond;
    }

    @Override
    public MatchConditions match(SyntaxElementCursor termPosition, MatchConditions matchConditions,
            Services services) {
        throw new UnsupportedOperationException();
    }

    @Override
    public MatchConditions match(Term instantiationCandidate, MatchConditions matchCond,
            Services services) {
        throw new UnsupportedOperationException();
    }

    }

    @Override
    public MatchConditions match(SyntaxElementCursor termPosition, MatchConditions matchConditions,
            Services services) {
        var term = (Term) termPosition.getCurrentNode();
        var variablesToMatchAndBind =
            term.boundVars();

        if (variablesToMatchAndBind.size() == boundVarBinders.length) {
            for (int i = 0; i < boundVarBinders.length && matchConditions != null; i++) {
                // concrete variables must be logic variables
                final LogicVariable qVar = (LogicVariable) variablesToMatchAndBind.get(i);
                matchConditions = boundVarBinders[i].match(qVar, matchConditions, services);
            }
        } else {
            matchConditions = null;
        }

        return matchConditions;
    }
}
