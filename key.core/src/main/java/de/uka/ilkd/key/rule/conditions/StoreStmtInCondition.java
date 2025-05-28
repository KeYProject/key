/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.LightweightSyntacticalReplaceVisitor;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.VariableCondition;
import org.key_project.prover.rules.instantiation.MatchConditions;
import org.key_project.prover.rules.instantiation.SVInstantiations;

/**
 * Stores the given {@link Statement}, after substitution of {@link SchemaVariable}s, into the given
 * {@link ProgramSV} for later use in other conditions and transformers. The arguments are a
 * {@link ProgramSV} and a {@link JTerm}, where the {@link JTerm} must contain a {@link JavaBlock}
 * with a {@link StatementBlock} containing <emph>a single statement</emph> (that works, e.g., when
 * passing an expression like
 * <code>\modality{#allmodal}{ while (#e) #body }\endmodality(post)</code>); this statement is then
 * stored (in the example the while statement).
 *
 * @author Dominic Steinhoefel
 */
public class StoreStmtInCondition implements VariableCondition {
    private final ProgramSV storeInSV;
    private final JTerm term;

    public StoreStmtInCondition(ProgramSV resultVarSV, JTerm term) {
        this.storeInSV = resultVarSV;
        this.term = term;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SyntaxElement instCandidate,
            MatchConditions matchCond, LogicServices services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(storeInSV) != null) {
            return matchCond;
        }

        final LightweightSyntacticalReplaceVisitor replVisitor = //
            new LightweightSyntacticalReplaceVisitor(
                (de.uka.ilkd.key.rule.inst.SVInstantiations) svInst, (Services) services);
        term.execPostOrder(replVisitor);
        final JTerm instantiatedTerm = replVisitor.getTerm();

        // We assume that the term has a JavaBlock and that consists of a StatementBlock
        // containing exactly one statement; see JavaDoc.

        assert !instantiatedTerm.javaBlock().isEmpty();
        assert instantiatedTerm.javaBlock().program() instanceof StatementBlock;
        assert instantiatedTerm.javaBlock().program().getChildCount() == 1;

        return matchCond.setInstantiations(//
            ((de.uka.ilkd.key.rule.inst.SVInstantiations) svInst).add(storeInSV,
                (Statement) instantiatedTerm.javaBlock().program().getFirstElement(), services));
    }

    @Override
    public String toString() {
        return String.format( //
            "\\varcond (\\storeStmtIn(%s, %s))", storeInSV, term);
    }

}
