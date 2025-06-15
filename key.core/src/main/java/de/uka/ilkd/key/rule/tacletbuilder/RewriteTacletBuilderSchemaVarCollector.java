/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Visitor;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;


/**
 *
 * @author christoph
 */
public class RewriteTacletBuilderSchemaVarCollector {

    private final RewriteTacletBuilder<? extends RewriteTaclet> rtb;


    public RewriteTacletBuilderSchemaVarCollector(
            RewriteTacletBuilder<? extends RewriteTaclet> rtb) {
        this.rtb = rtb;
    }


    public Set<SchemaVariable> collectSchemaVariables() {

        Set<SchemaVariable> result = new LinkedHashSet<>(collectSchemaVariables(rtb.ifSequent()));

        if (rtb instanceof FindTacletBuilder) {
            result.addAll(collectSchemaVariables(rtb.getFind()));
        }

        for (var tgt : rtb.goalTemplates()) {
            result.addAll(collectSchemaVariables(tgt));
            for (var tacletInAddrules : tgt.rules()) {
                result.addAll(((Taclet) tacletInAddrules).collectSchemaVars());
            }
        }

        return result;
    }

    private Set<SchemaVariable> collectSchemaVariables(SyntaxElement se) {
        if (se instanceof JTerm t)
            return collectSchemaVariables(t);
        else if (se instanceof Sequent s)
            return collectSchemaVariables(s);
        else
            throw new IllegalArgumentException("Unhandled syntax element: " + se);
    }

    private Set<SchemaVariable> collectSchemaVariables(JTerm t) {
        final Set<SchemaVariable> result = new LinkedHashSet<>();

        t.execPreOrder(new Visitor<JTerm>() {
            @Override
            public boolean visitSubtree(JTerm visited) {
                return true;
            }

            @Override
            public void visit(JTerm visited) {
                if (visited.op() instanceof SchemaVariable) {
                    result.add((SchemaVariable) visited.op());
                }
            }


            @Override
            public void subtreeEntered(JTerm subtreeRoot) {
                // nothing to do
            }


            @Override
            public void subtreeLeft(JTerm subtreeRoot) {
                // nothing to do
            }
        });

        return result;
    }


    private Set<SchemaVariable> collectSchemaVariables(Sequent s) {
        Set<SchemaVariable> result = new LinkedHashSet<>();

        for (final SequentFormula cf : s) {
            result.addAll(collectSchemaVariables((JTerm) cf.formula()));
        }

        return result;
    }


    private Set<SchemaVariable> collectSchemaVariables(TacletGoalTemplate templ) {

        Set<SchemaVariable> result = new LinkedHashSet<>(collectSchemaVariables(templ.sequent()));
        if (templ instanceof RewriteTacletGoalTemplate) {
            result.addAll(
                collectSchemaVariables(((RewriteTacletGoalTemplate) templ).replaceWith()));
        }
        if (templ instanceof AntecSuccTacletGoalTemplate) {
            result.addAll(
                collectSchemaVariables(((AntecSuccTacletGoalTemplate) templ).replaceWith()));
        }

        return result;
    }
}
