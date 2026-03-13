/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;
import org.key_project.util.collection.ImmutableArray;

/**
 * This instruction matches the variable below a binder (e.g. a quantifier).
 */
public class BindVariablesInstruction implements MatchInstruction {

    private final VariableBinderSubinstruction[] boundVarBinders;

    public BindVariablesInstruction(ImmutableArray<QuantifiableVariable> boundVars) {
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
                MatchConditions matchCond, LogicServices services);
    }

    private record LogicVariableBinder(LogicVariable templateVar)
            implements VariableBinderSubinstruction {

        /**
         * a match between two logic variables is possible if they have been assigned they are same
         * or have been assigned to the same abstract name and the sorts are equal.
         */
        public MatchConditions match(LogicVariable instantiationCandidate,
                MatchConditions matchCond, LogicServices services) {
            final RenameTable rt = matchCond.renameTable();
            if (!rt.containsLocally(templateVar) && !rt.containsLocally(instantiationCandidate)) {
                matchCond = matchCond.addRenaming(templateVar, instantiationCandidate);
            }

            if (templateVar != instantiationCandidate) {
                if (instantiationCandidate.sort() != templateVar.sort() || !matchCond.renameTable()
                        .sameAbstractName(templateVar, instantiationCandidate)) {
                    matchCond = null;
                }
            }
            return matchCond;
        }
    }

    private static class VariableSVBinder extends MatchSchemaVariableInstruction
            implements VariableBinderSubinstruction {

        public VariableSVBinder(VariableSV templateVar) {
            super(templateVar);
        }

        @Override
        public MatchConditions match(LogicVariable instantiationCandidate,
                MatchConditions matchCond, LogicServices p_services) {
            final Services services = (Services) p_services;
            final Object foundMapping = matchCond.getInstantiations().getInstantiation(op);
            if (foundMapping == null) {
                final JTerm substTerm = services.getTermBuilder().var(instantiationCandidate);
                return addInstantiation(substTerm, matchCond, services);
            } else if (((JTerm) foundMapping).op() != instantiationCandidate) {
                return null;
            } else {
                return matchCond;
            }
        }

        @Override
        public MatchResultInfo match(SyntaxElement actualElement,
                MatchResultInfo matchConditions,
                LogicServices services) {
            throw new UnsupportedOperationException();
        }
    }

    @Override
    public MatchResultInfo match(SyntaxElement actualElement, MatchResultInfo matchResult,
            LogicServices services) {
        MatchConditions matchConditions = (MatchConditions) matchResult;
        final ImmutableArray<QuantifiableVariable> variablesToMatchAndBind =
            ((JTerm) actualElement).boundVars();
        matchConditions = matchConditions.extendRenameTable();
        if (variablesToMatchAndBind.size() == boundVarBinders.length) {
            for (int i = 0; i < boundVarBinders.length && matchConditions != null; i++) {
                // concrete variables must be logic variables
                final LogicVariable qVar = (LogicVariable) variablesToMatchAndBind.get(i);
                matchConditions = boundVarBinders[i].match(qVar, matchConditions, services);
            }
            return matchConditions;
        }
        return null;
    }

}
