/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.tacletbuilder;


import java.util.Iterator;

import org.key_project.logic.Term;
import org.key_project.rusty.logic.Sequent;
import org.key_project.rusty.logic.SequentFormula;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.sv.*;
import org.key_project.rusty.rule.*;
import org.key_project.util.collection.*;


public class TacletPrefixBuilder {
    /**
     * set of all schemavariables that are only allowed to be matched with quantifiable variables.
     */
    private int numberOfCurrentlyBoundVars =
        0;
    private final TacletBuilder<? extends Taclet> tacletBuilder;

    protected ImmutableMap<SchemaVariable, TacletPrefix> prefixMap =
        DefaultImmutableMap.nilMap();

    public TacletPrefixBuilder(TacletBuilder<? extends Taclet> tacletBuilder) {
        this.tacletBuilder = tacletBuilder;
    }

    private void addVarsBoundHere(Term visited, int subTerm) {
        numberOfCurrentlyBoundVars += visited.varsBoundHere(subTerm).size();
    }

    private void setPrefixOfOccurrence(SchemaVariable sv,
            int numberOfBoundVars) {
        prefixMap = prefixMap.put(sv, new TacletPrefix(numberOfBoundVars, false));
    }

    /**
     * removes all variables x that are declared as x not free in sv from the currently bound vars
     * set.
     */
    private int removeNotFreeIn(SchemaVariable sv) {
        int result = numberOfCurrentlyBoundVars;
        Iterator<NotFreeIn> it = tacletBuilder.varsNotFreeIn();
        while (it.hasNext()) {
            NotFreeIn notFreeIn = it.next();
            if (notFreeIn.second() == sv) {
                // TODO: result = result.remove(notFreeIn.first());
            }
        }
        return result;
    }

    private void visit(Term t) {
        if (t.op() instanceof Modality mod && mod.kind() instanceof ModalOperatorSV msv) {
            // TODO: Is false correct?
            prefixMap.put(msv, new TacletPrefix(0, false));
        }
        if (t.op() instanceof SchemaVariable sv && t.arity() == 0) {
            if (sv instanceof TermSV || sv instanceof FormulaSV || sv instanceof UpdateSV) {
                int numberOfBoundVars = removeNotFreeIn(sv);
                TacletPrefix prefix = prefixMap.get(sv);
                if (prefix == null || prefix.prefixLength() == numberOfBoundVars) {
                    setPrefixOfOccurrence(sv, numberOfBoundVars);
                } else {
                    // TODO: For now, don't report an error. It's likely not needed
                    /*
                     * throw new TacletPrefixBuilder.InvalidPrefixException(
                     * tacletBuilder.getName().toString(), sv, prefix,
                     * numberOfBoundVars);
                     */
                }
            }
        }
        for (int i = 0; i < t.arity(); i++) {
            int oldBounds = numberOfCurrentlyBoundVars;
            addVarsBoundHere(t, i);
            visit(t.sub(i));
            numberOfCurrentlyBoundVars = oldBounds;
        }

        // if (t.hasLabels()) {
        // for (TermLabel l : t.getLabels()) {
        // if (l instanceof SchemaVariable sv) {
        // ImmutableSet<SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
        // TacletPrefix prefix = prefixMap.get(sv);
        // if (prefix == null || prefix.prefix().equals(relevantBoundVars)) {
        // setPrefixOfOccurrence(sv, relevantBoundVars);
        // } else {
        // throw new
        // de.uka.ilkd.key.rule.tacletbuilder.TacletPrefixBuilder.InvalidPrefixException(tacletBuilder.getName().toString(),
        // sv,
        // prefix, relevantBoundVars);
        // }
        // }
        // }
        // }
    }

    private void visit(Sequent s) {
        for (final SequentFormula cf : s) {
            visit(cf.formula());
        }
    }

    private void visit(TacletGoalTemplate templ) {
        visit(templ.sequent());
        if (templ instanceof RewriteTacletGoalTemplate rtgt) {
            visit(rtgt.replaceWith());
        }
        if (templ instanceof AntecSuccTacletGoalTemplate astgt) {
            visit(astgt.replaceWith());
        }
    }

    public void build() {
        visit(tacletBuilder.ifSequent());

        if (tacletBuilder instanceof FindTacletBuilder<? extends FindTaclet> ftb) {
            final Term find = ftb.getFind();
            visit(find);
        }

        for (final TacletGoalTemplate tgt : tacletBuilder.goalTemplates()) {
            visit(tgt);
            for (Taclet tacletInAddRule : tgt.rules()) {
                checkPrefixInAddRules(tacletInAddRule);
            }
        }
    }


    private void checkPrefixInAddRules(Taclet addRule) {
        final ImmutableMap<SchemaVariable, TacletPrefix> addRuleSV2PrefixMap = addRule.prefixMap();
        for (final ImmutableMapEntry<SchemaVariable, TacletPrefix> entry : prefixMap) {
            final TacletPrefix addRulePrefix = addRuleSV2PrefixMap.get(entry.key());

            if (addRulePrefix != null
                    && addRulePrefix.prefixLength() != entry.value().prefixLength()) {
                throw new TacletPrefixBuilder.InvalidPrefixException(
                    tacletBuilder.getName().toString(), entry.key(),
                    entry.value(), addRulePrefix.prefixLength());
            }
        }

        // we have to descend into the addrules of the addrules

        for (TacletGoalTemplate tacletGoalTemplate : addRule.goalTemplates()) {
            for (Taclet taclet : tacletGoalTemplate.rules()) {
                checkPrefixInAddRules(taclet);
            }
        }
    }


    private boolean atMostOneRepl() {
        RewriteTacletBuilder<? extends RewriteTaclet> rwtacletBuilder =
            (RewriteTacletBuilder<? extends RewriteTaclet>) tacletBuilder;
        int count = 0;
        for (TacletGoalTemplate tmpl : rwtacletBuilder.goalTemplates()) {
            if (tmpl instanceof RewriteTacletGoalTemplate rtgt) {
                if (rtgt.replaceWith() != null) {
                    count++;
                }
            }
            if (count > 1) {
                return false;
            }
        }
        return true;
    }

    private boolean occurrsOnlyInFindOrRepl(SchemaVariable sv) {
        RewriteTacletBuilder<? extends RewriteTaclet> rwtacletBuilder =
            (RewriteTacletBuilder<? extends RewriteTaclet>) tacletBuilder;
        TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector();
        svc.visit(rwtacletBuilder.ifSequent());
        for (TacletGoalTemplate tacletGoalTemplate : rwtacletBuilder.goalTemplates()) {
            TacletGoalTemplate tmpl = tacletGoalTemplate;
            // if (tmpl instanceof RewriteTacletGoalTemplate) {
            // RewriteTacletGoalTemplate
            // gt=(RewriteTacletGoalTemplate)tmpl;
            svc.visit(tmpl.sequent());
            for (Taclet taclet : tmpl.rules()) { // addrules
                svc.visit(taclet, true);
            }
        }
        // }
        return !svc.contains(sv);
    }

    private void considerContext() {
        if (!(tacletBuilder instanceof RewriteTacletBuilder) || !atMostOneRepl()) {
            return;
        }
        for (final ImmutableMapEntry<SchemaVariable, TacletPrefix> entry : prefixMap) {
            if (occurrsOnlyInFindOrRepl(entry.key())) {
                prefixMap = prefixMap.put(entry.key(), entry.value().setContext(true));
            }
        }
    }

    public ImmutableMap<SchemaVariable, TacletPrefix> getPrefixMap() {
        considerContext();
        return prefixMap;
    }

    public static class InvalidPrefixException extends IllegalStateException {
        private static final long serialVersionUID = 5855187579027274363L;

        InvalidPrefixException(String tacletName, SchemaVariable sv, TacletPrefix prefix,
                int numberOfBoundVars) {
            super("Schema variable " + sv + "occurs at different places " + "in taclet "
                + tacletName + " with different prefixes.\n" + "Prefix P1:"
                + ((prefix == null) ? 0 : prefix.prefixLength())
                + "\n" + "Prefix P2:" + numberOfBoundVars);
        }

    }
}
