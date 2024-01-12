/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;


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

        for (TacletGoalTemplate tgt : rtb.goalTemplates()) {
            result.addAll(collectSchemaVariables(tgt));
            for (Taclet tacletInAddrules : tgt.rules()) {
                result.addAll(tacletInAddrules.collectSchemaVars());
            }
        }

        return result;
    }


    private Set<SchemaVariable> collectSchemaVariables(Term t) {
        final Set<SchemaVariable> result = new LinkedHashSet<>();

        t.execPreOrder(new Visitor() {
            @Override
            public boolean visitSubtree(Term visited) {
                return true;
            }

            @Override
            public void visit(Term visited) {
                if (visited.op() instanceof SchemaVariable) {
                    result.add((SchemaVariable) visited.op());
                }
            }


            @Override
            public void subtreeEntered(Term subtreeRoot) {
                // nothing to do
            }


            @Override
            public void subtreeLeft(Term subtreeRoot) {
                // nothing to do
            }
        });

        return result;
    }


    private Set<SchemaVariable> collectSchemaVariables(Sequent s) {
        Set<SchemaVariable> result = new LinkedHashSet<>();

        for (final SequentFormula cf : s) {
            result.addAll(collectSchemaVariables(cf.formula()));
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
