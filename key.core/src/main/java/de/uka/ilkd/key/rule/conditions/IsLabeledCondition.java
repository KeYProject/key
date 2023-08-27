/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import java.util.ArrayList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Checks whether the given statement is labeled, i.e., actual a LabeledStatement. This information
 * is obtained from the program prefix.
 *
 * @author Dominic Steinhoefel
 */
public class IsLabeledCondition implements VariableCondition {
    private final boolean negated;
    private final ProgramSV stmtSV;

    public IsLabeledCondition(ProgramSV stmtSV, boolean negated) {
        this.stmtSV = stmtSV;
        this.negated = negated;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        final JavaStatement stmt = (JavaStatement) svInst.getInstantiation(stmtSV);

        final ArrayList<ProgramElement> labels = new ArrayList<>();
        ProgramPrefix prefix = //
            (ProgramPrefix) svInst.getContextInstantiation().contextProgram();
        do {
            if (prefix instanceof LabeledStatement
                    && ((LabeledStatement) prefix).getBody().equals(stmt)) {
                labels.add(((LabeledStatement) prefix).getLabel());
            }
        } while (prefix.hasNextPrefixElement() && (prefix = prefix.getNextPrefixElement()) != null);

        if (labels.isEmpty()) {
            return negated ? matchCond : null;
        } else {
            return negated ? null : matchCond;
        }
    }

    @Override
    public String toString() {
        return String.format("\\varcond (%s\\isLabeled(%s)", negated ? "\\not" : "", stmtSV);
    }
}
