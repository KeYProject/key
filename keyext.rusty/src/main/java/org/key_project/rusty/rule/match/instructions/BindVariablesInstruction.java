/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.BoundVariable;
import org.key_project.rusty.logic.op.sv.VariableSV;

import org.jspecify.annotations.NonNull;

/** This instructions matches the variable below a binder (e.g. a quantifier). */
public class BindVariablesInstruction {

    public static MatchInstruction create(QuantifiableVariable var) {
        if (var instanceof BoundVariable bv) {
            return new LogicVariableBinder(bv);
        } else {
            return new VariableSVBinder((VariableSV) var);
        }
    }

    private record LogicVariableBinder(BoundVariable templateVar)
            implements MatchInstruction {

        /**
         * a match between two logic variables is possible if they have been assigned they are same
         * or
         * have been assigned to the same abstract name and the sorts are equal.
         */
        private MatchConditions match(
                BoundVariable instantiationCandidate, MatchConditions matchCond,
                LogicServices services) {
            if (templateVar != instantiationCandidate) {
                if (instantiationCandidate.sort() != templateVar.sort()) {
                    matchCond = null;
                }
            }
            return matchCond;
        }

        @Override
        public MatchConditions match(
                SyntaxElementCursor cursor,
                MatchConditions matchConditions, LogicServices services) {
            var node = cursor.getCurrentNode();
            if (!(node instanceof BoundVariable bv)) {
                return null;
            }
            var result = match(bv, matchConditions, services);
            cursor.gotoNextSibling();
            return result;
        }
    }


    private static class VariableSVBinder
            extends MatchSchemaVariableInstruction<@NonNull VariableSV> {

        public VariableSVBinder(VariableSV templateVar) {
            super(templateVar);
        }

        private MatchConditions match(
                BoundVariable instantiationCandidate, MatchConditions matchCond,
                Services services) {
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
        public MatchConditions match(
                SyntaxElementCursor cursor, MatchConditions matchConditions,
                LogicServices services) {
            var node = cursor.getCurrentNode();
            if (!(node instanceof BoundVariable bv)) {
                return null;
            }
            var result = match(bv, matchConditions, (Services) services);
            cursor.gotoNextSibling();
            return result;
        }

        @Override
        public MatchConditions match(
                Term instantiationCandidate, MatchConditions matchCond, LogicServices services) {
            throw new UnsupportedOperationException();
        }
    }
}
