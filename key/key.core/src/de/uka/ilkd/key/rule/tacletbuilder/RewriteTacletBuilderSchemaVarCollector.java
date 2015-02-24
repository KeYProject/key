/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.Taclet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;


/**
 *
 * @author christoph
 */
public class RewriteTacletBuilderSchemaVarCollector {

    private final RewriteTacletBuilder rtb;


    public RewriteTacletBuilderSchemaVarCollector(RewriteTacletBuilder rtb) {
        this.rtb = rtb;
    }


    public Set<SchemaVariable> collectSchemaVariables() {
        Set<SchemaVariable> result = new LinkedHashSet<SchemaVariable>();

        result.addAll(collectSchemaVariables(rtb.ifSequent()));

        if (rtb instanceof FindTacletBuilder) {
            result.addAll(collectSchemaVariables(((FindTacletBuilder) rtb).getFind()));
        }

        Iterator<TacletGoalTemplate> itGoalTempl =
                rtb.goalTemplates().iterator();

        while (itGoalTempl.hasNext()) {
            result.addAll(collectSchemaVariables(itGoalTempl.next()));
        }

        itGoalTempl = rtb.goalTemplates().iterator();
        while (itGoalTempl.hasNext()) {
            final Iterator<Taclet> addRules =
                    itGoalTempl.next().rules().iterator();
            while (addRules.hasNext()) {
                result.addAll(addRules.next().collectSchemaVars());
            }
        }

        return result;
    }


    private Set<SchemaVariable> collectSchemaVariables(Term t) {
        final Set<SchemaVariable> result = new LinkedHashSet<SchemaVariable>();

        t.execPreOrder(new Visitor() {
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
        Set<SchemaVariable> result = new LinkedHashSet<SchemaVariable>();

        for (final SequentFormula cf : s) {
            result.addAll(collectSchemaVariables(cf.formula()));
        }

        return result;
    }


    private Set<SchemaVariable> collectSchemaVariables(TacletGoalTemplate templ) {
        Set<SchemaVariable> result = new LinkedHashSet<SchemaVariable>();

        result.addAll(collectSchemaVariables(templ.sequent()));
        if (templ instanceof RewriteTacletGoalTemplate) {
            result.addAll(collectSchemaVariables(((RewriteTacletGoalTemplate) templ).replaceWith()));
        }
        if (templ instanceof AntecSuccTacletGoalTemplate) {
            result.addAll(collectSchemaVariables(((AntecSuccTacletGoalTemplate) templ).replaceWith()));
        }

        return result;
    }
}
