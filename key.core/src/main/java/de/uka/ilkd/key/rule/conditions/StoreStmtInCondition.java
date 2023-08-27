/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.LightweightSyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Stores the given {@link Statement}, after substitution of {@link SchemaVariable}s, into the given
 * {@link ProgramSV} for later use in other conditions and transformers. The arguments are a
 * {@link ProgramSV} and a {@link Term}, where the {@link Term} must contain a {@link JavaBlock}
 * with a {@link StatementBlock} containing <emph>a single statement</emph> (that works, e.g., when
 * passing an expression like
 * <code>\modality{#allmodal}{ while (#e) #body }\endmodality(post)</code>); this statement is then
 * stored (in the example the while statement).
 *
 * @author Dominic Steinhoefel
 */
public class StoreStmtInCondition implements VariableCondition {
    private final ProgramSV storeInSV;
    private final Term term;

    public StoreStmtInCondition(ProgramSV resultVarSV, Term term) {
        this.storeInSV = resultVarSV;
        this.term = term;
    }

    @Override
    public MatchConditions check(SchemaVariable sv, SVSubstitute instCandidate,
            MatchConditions matchCond, Services services) {
        final SVInstantiations svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(storeInSV) != null) {
            return matchCond;
        }

        final LightweightSyntacticalReplaceVisitor replVisitor = //
            new LightweightSyntacticalReplaceVisitor(svInst, services);
        term.execPostOrder(replVisitor);
        final Term instantiatedTerm = replVisitor.getTerm();

        // We assume that the term has a JavaBlock and that consists of a StatementBlock
        // containing exactly one statement; see JavaDoc.

        assert !instantiatedTerm.javaBlock().isEmpty();
        assert instantiatedTerm.javaBlock().program() instanceof StatementBlock;
        assert ((StatementBlock) instantiatedTerm.javaBlock().program()).getChildCount() == 1;

        return matchCond.setInstantiations(//
            svInst.add(storeInSV,
                (Statement) instantiatedTerm.javaBlock().program().getFirstElement(), services));
    }

    @Override
    public String toString() {
        return String.format( //
            "\\varcond (\\storeStmtIn(%s, %s))", storeInSV, term);
    }

}
