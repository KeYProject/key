/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.varcond;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.ProgramSV;
import org.key_project.rusty.rule.LightweightSyntacticalReplaceVisitor;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.rusty.rule.VariableCondition;

/**
 * Stores the given {@link org.key_project.rusty.ast.expr.Expr}, after substitution of
 * {@link SchemaVariable}s, into the given
 * {@link ProgramSV} for later use in other conditions and transformers. The arguments are a
 * {@link ProgramSV} and a {@link Term}, where the {@link Term} must contain a
 * {@link org.key_project.rusty.logic.RustyBlock}
 * with a {@link org.key_project.rusty.ast.expr.BlockExpression} containing <emph>a single
 * expression</emph> (that works, e.g., when
 * passing an expression like
 * <code>\modality{#allmodal}{ loop s#body }\endmodality(post)</code>); this expr is then
 * stored (in the example the loop expr).
 *
 * @author Dominic Steinhoefel
 */
public class StoreExprInCondition implements VariableCondition {
    private final ProgramSV storeInSV;
    private final Term term;

    public StoreExprInCondition(ProgramSV storeInSV, Term term) {
        this.term = term;
        this.storeInSV = storeInSV;
    }

    @Override
    public MatchConditions check(SchemaVariable var, SyntaxElement instCandidate,
            MatchConditions matchCond, Services services) {
        final var svInst = matchCond.getInstantiations();

        if (svInst.getInstantiation(storeInSV) != null) {
            return matchCond;
        }

        final LightweightSyntacticalReplaceVisitor replVisitor =
            new LightweightSyntacticalReplaceVisitor(svInst, services);
        term.execPostOrder(replVisitor);
        final Term instantiatedTerm = replVisitor.getTerm();

        // We assume that the term has a RustyBlock and that consists of a BlockExpression
        // containing exactly one statement; see JavaDoc.

        var mod = (Modality) instantiatedTerm.op();
        var be = (BlockExpression) mod.program().program();
        assert be.getValue() != null;

        return matchCond.setInstantiations(svInst.add(storeInSV, be.getValue(), services));
    }
}
