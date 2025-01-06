/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.*;

import org.key_project.prover.rules.NotFreeIn;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.*;

public class TacletPrefixBuilder {

    /**
     * set of all schemavariables that are only allowed to be matched with quantifiable variables.
     */
    private ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> currentlyBoundVars = DefaultImmutableSet.nil();
    private final TacletBuilder<? extends Taclet> tacletBuilder;

    protected ImmutableMap<org.key_project.logic.op.sv.SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap = DefaultImmutableMap.nilMap();

    public TacletPrefixBuilder(TacletBuilder<? extends Taclet> tacletBuilder) {
        this.tacletBuilder = tacletBuilder;
    }

    private void addVarsBoundHere(Term visited, int subTerm) {
        ImmutableArray<QuantifiableVariable> bdVars = visited.varsBoundHere(subTerm);
        for (int i = 0; i < bdVars.size(); i++) {
            QuantifiableVariable boundVar = bdVars.get(i);
            if (boundVar instanceof VariableSV) {
                currentlyBoundVars = currentlyBoundVars.add((SchemaVariable) boundVar);
            }
        }
    }

    private void setPrefixOfOccurrence(org.key_project.logic.op.sv.SchemaVariable sv,
            ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> relevantBoundVars) {
        prefixMap = prefixMap.put(sv, new TacletPrefix(relevantBoundVars, false));
    }

    /**
     * removes all variables x that are declared as x not free in sv from the currently bound vars
     * set.
     */
    private ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> removeNotFreeIn(SchemaVariable sv) {
        ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> result = currentlyBoundVars;
        Iterator<NotFreeIn> it = tacletBuilder.varsNotFreeIn();
        while (it.hasNext()) {
            NotFreeIn notFreeIn = it.next();
            if (notFreeIn.second() == sv) {
                result = result.remove(notFreeIn.first());
            }
        }
        return result;
    }

    private void visit(Term t) {
        if (t.op() instanceof Modality mod && mod.kind() instanceof ModalOperatorSV msv) {
            // TODO: Is false correct?
            prefixMap.put(msv, new TacletPrefix(ImmutableSet.empty(), false));
        }
        if (t.op() instanceof SchemaVariable sv && t.arity() == 0) {
            if (sv instanceof TermSV || sv instanceof FormulaSV || sv instanceof UpdateSV) {
                ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
                TacletPrefix prefix = (TacletPrefix) prefixMap.get(sv);
                if (prefix == null || prefix.prefix().equals(relevantBoundVars)) {
                    setPrefixOfOccurrence(sv, relevantBoundVars);
                } else {
                    throw new InvalidPrefixException(tacletBuilder.getName().toString(), sv, prefix,
                        relevantBoundVars);
                }
            }
        }
        for (int i = 0; i < t.arity(); i++) {
            ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> oldBounds = currentlyBoundVars;
            addVarsBoundHere(t, i);
            visit(t.sub(i));
            currentlyBoundVars = oldBounds;
        }

        if (t.hasLabels()) {
            for (TermLabel l : t.getLabels()) {
                if (l instanceof SchemaVariable sv) {
                    ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
                    TacletPrefix prefix = (TacletPrefix) prefixMap.get(sv);
                    if (prefix == null || prefix.prefix().equals(relevantBoundVars)) {
                        setPrefixOfOccurrence(sv, relevantBoundVars);
                    } else {
                        throw new InvalidPrefixException(tacletBuilder.getName().toString(), sv,
                            prefix, relevantBoundVars);
                    }
                }
            }
        }
    }

    private void visit(Sequent s) {
        for (final SequentFormula cf : s) {
            visit((Term) cf.formula());
        }
    }

    private void visit(org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate templ) {
        visit(templ.sequent());
        if (templ instanceof RewriteTacletGoalTemplate) {
            visit(((RewriteTacletGoalTemplate) templ).replaceWith());
        }
        if (templ instanceof AntecSuccTacletGoalTemplate) {
            visit(((AntecSuccTacletGoalTemplate) templ).replaceWith());
        }
    }

    public void build() {
        visit(tacletBuilder.ifSequent());

        if (tacletBuilder instanceof FindTacletBuilder) {
            @SuppressWarnings("unchecked")
            final Term find = ((FindTacletBuilder<? extends FindTaclet>) tacletBuilder).getFind();
            visit(find);
        }

        for (final var tgt : tacletBuilder.goalTemplates()) {
            visit(tgt);
            for (var tacletInAddRule : tgt.rules()) {
                checkPrefixInAddRules(tacletInAddRule);
            }
        }
    }


    private void checkPrefixInAddRules(org.key_project.prover.rules.Taclet addRule) {
        final ImmutableMap<org.key_project.logic.op.sv.SchemaVariable,
                org.key_project.prover.rules.TacletPrefix> addRuleSV2PrefixMap = addRule.prefixMap();
        for (final var entry : prefixMap) {
            final TacletPrefix addRulePrefix = (TacletPrefix) addRuleSV2PrefixMap.get(entry.key());

            if (addRulePrefix != null) {
                TacletPrefix prefix = (TacletPrefix) entry.value();
                if (!addRulePrefix.prefix().equals(prefix.prefix())) {
                    throw new InvalidPrefixException(tacletBuilder.getName().toString(), entry.key(),
                            prefix, addRulePrefix.prefix());
                }
            }
        }

        // we have to descend into the addrules of the addrules

        for (var tacletGoalTemplate : addRule.goalTemplates()) {
            for (var taclet : tacletGoalTemplate.rules()) {
                checkPrefixInAddRules(taclet);
            }
        }
    }


    private boolean atMostOneRepl() {
        @SuppressWarnings("unchecked")
        RewriteTacletBuilder<? extends RewriteTaclet> rwtacletBuilder =
            (RewriteTacletBuilder<? extends RewriteTaclet>) tacletBuilder;
        int count = 0;
        for (var tmpl : rwtacletBuilder.goalTemplates()) {
            if (tmpl instanceof RewriteTacletGoalTemplate rwTemplate) {
                if (rwTemplate.replaceWith() != null) {
                    count++;
                }
            }
            if (count > 1) {
                return false;
            }
        }
        return true;
    }

    private boolean occurrsOnlyInFindOrRepl(org.key_project.logic.op.sv.SchemaVariable sv) {
        @SuppressWarnings("unchecked")
        RewriteTacletBuilder<? extends RewriteTaclet> rwtacletBuilder =
            (RewriteTacletBuilder<? extends RewriteTaclet>) tacletBuilder;
        TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector();
        svc.visit(rwtacletBuilder.ifSequent());
        for (var tacletGoalTemplate : rwtacletBuilder.goalTemplates()) {
            // if (tmpl instanceof RewriteTacletGoalTemplate) {
            // RewriteTacletGoalTemplate
            // gt=(RewriteTacletGoalTemplate)tmpl;
            svc.visit(tacletGoalTemplate.sequent());
            for (var taclet : tacletGoalTemplate.rules()) { // addrules
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
        for (final var entry : prefixMap) {
            if (occurrsOnlyInFindOrRepl(entry.key())) {
                prefixMap = prefixMap.put(entry.key(), entry.value().setContext(true));
            }
        }
    }

    public ImmutableMap<org.key_project.logic.op.sv.SchemaVariable, org.key_project.prover.rules.TacletPrefix> getPrefixMap() {
        considerContext();
        return prefixMap;
    }

    public static class InvalidPrefixException extends IllegalStateException {
        private static final long serialVersionUID = 5855187579027274363L;

        InvalidPrefixException(String tacletName, org.key_project.logic.op.sv.SchemaVariable sv, org.key_project.prover.rules.TacletPrefix prefix,
                               ImmutableSet<org.key_project.logic.op.sv.SchemaVariable> sndPrefixVar) {
            super("Schema variable " + sv + "occurs at different places " + "in taclet "
                + tacletName + " with different prefixes.\n" + "Prefix P1:"
                + ((prefix == null) ? DefaultImmutableSet.<SchemaVariable>nil() : prefix)
                + "\n" + "Prefix P2:" + sndPrefixVar);
        }

    }

}
