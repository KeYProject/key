/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.LightweightSyntacticalReplaceVisitor;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.MatchConditions;
import org.key_project.prover.rules.VariableCondition;

/**
 * Stores the given {@link Term}, after substitution of {@link SchemaVariable}s, into the given
 * {@link SchemaVariable} for later use in other conditions and transformers.
 *
 * @author Dominic Steinhoefel
 */
public class StoreTermInCondition implements VariableCondition {
    private final SchemaVariable storeInSV;
    private final Term term;

    public StoreTermInCondition(SchemaVariable resultVarSV, Term term) {
        this.storeInSV = resultVarSV;
        this.term = term;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SyntaxElement instCandidate,
            MatchConditions matchCond, LogicServices services) {
        final var svInst =
            (de.uka.ilkd.key.rule.inst.SVInstantiations) matchCond.getInstantiations();

        if (svInst.getInstantiation(storeInSV) != null) {
            return matchCond;
        }

        final LightweightSyntacticalReplaceVisitor replVisitor = //
            new LightweightSyntacticalReplaceVisitor(svInst, (Services) services);
        term.execPostOrder(replVisitor);
        final Term instantiatedTerm = replVisitor.getTerm();

        return matchCond.setInstantiations( //
            svInst.add(storeInSV, instantiatedTerm, services));
    }

    @Override
    public String toString() {
        return String.format( //
            "\\varcond (\\storeTermIn(%s, %s))", storeInSV, term);
    }

}
