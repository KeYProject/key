/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.Iterator;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.*;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Modality;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.conditions.NotFreeIn;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.*;

public class TacletPrefixBuilder {

    /**
     * set of all schemavariables that are only allowed to be matched with quantifiable variables.
     */
    private ImmutableSet<SchemaVariable> currentlyBoundVars =
        DefaultImmutableSet.nil();
    private final TacletBuilder<? extends Taclet> tacletBuilder;

    protected ImmutableMap<SchemaVariable, org.key_project.prover.rules.TacletPrefix> prefixMap =
        DefaultImmutableMap.nilMap();

    public TacletPrefixBuilder(TacletBuilder<? extends Taclet> tacletBuilder) {
        this.tacletBuilder = tacletBuilder;
    }

    private void addVarsBoundHere(JTerm visited, int subTerm) {
        ImmutableArray<QuantifiableVariable> bdVars = visited.varsBoundHere(subTerm);
        for (int i = 0; i < bdVars.size(); i++) {
            QuantifiableVariable boundVar = bdVars.get(i);
            if (boundVar instanceof VariableSV boundSV) {
                currentlyBoundVars = currentlyBoundVars.add(boundSV);
            }
        }
    }

    private void setPrefixOfOccurrence(SchemaVariable sv,
            ImmutableSet<SchemaVariable> relevantBoundVars) {
        prefixMap = prefixMap.put(sv, new TacletPrefix(relevantBoundVars, false));
    }

    /**
     * removes all variables x that are declared as x not free in sv from the currently bound vars
     * set.
     */
    private ImmutableSet<SchemaVariable> removeNotFreeIn(
            SchemaVariable sv) {
        ImmutableSet<SchemaVariable> result = currentlyBoundVars;
        Iterator<NotFreeIn> it = tacletBuilder.varsNotFreeIn();
        while (it.hasNext()) {
            NotFreeIn notFreeIn = it.next();
            if (notFreeIn.second() == sv) {
                result = result.remove(notFreeIn.first());
            }
        }
        return result;
    }

    private void visit(JTerm t) {
        if (t.op() instanceof Modality mod && mod.kind() instanceof ModalOperatorSV msv) {
            // TODO: Is false correct?
            prefixMap.put(msv, new TacletPrefix(ImmutableSet.empty(), false));
        }
        if (t.op() instanceof SchemaVariable sv && t.arity() == 0) {
            if (sv instanceof TermSV || sv instanceof FormulaSV || sv instanceof UpdateSV) {
                ImmutableSet<SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
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
            ImmutableSet<SchemaVariable> oldBounds = currentlyBoundVars;
            addVarsBoundHere(t, i);
            visit(t.sub(i));
            currentlyBoundVars = oldBounds;
        }

        if (t.hasLabels()) {
            for (TermLabel l : t.getLabels()) {
                if (l instanceof SchemaVariable sv) {
                    ImmutableSet<SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
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
            visit((JTerm) cf.formula());
        }
    }

    private void visit(org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate templ) {
        visit(templ.sequent());
        if (templ instanceof RewriteTacletGoalTemplate rwTemplate) {
            visit(rwTemplate.replaceWith());
        }
        if (templ instanceof AntecSuccTacletGoalTemplate antecSuccTemplate) {
            visit(antecSuccTemplate.replaceWith());
        }
    }

    public void build() {
        visit(tacletBuilder.ifSequent());

        if (tacletBuilder instanceof FindTacletBuilder findBuilder) {
            @SuppressWarnings("unchecked")
            final SyntaxElement find = findBuilder.getFind();
            if (find instanceof JTerm t)
                visit(t);
            else if (find instanceof Sequent s)
                visit(s);
        }

        for (final var tgt : tacletBuilder.goalTemplates()) {
            visit(tgt);
            for (var tacletInAddRule : tgt.rules()) {
                checkPrefixInAddRules(tacletInAddRule);
            }
        }
    }


    private void checkPrefixInAddRules(org.key_project.prover.rules.Taclet addRule) {
        final ImmutableMap<SchemaVariable, org.key_project.prover.rules.TacletPrefix> addRuleSV2PrefixMap =
            addRule.prefixMap();
        for (final var entry : prefixMap) {
            final TacletPrefix addRulePrefix = (TacletPrefix) addRuleSV2PrefixMap.get(entry.key());

            if (addRulePrefix != null) {
                TacletPrefix prefix = (TacletPrefix) entry.value();
                if (!addRulePrefix.prefix().equals(prefix.prefix())) {
                    throw new InvalidPrefixException(tacletBuilder.getName().toString(),
                        entry.key(),
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
        int count = 0;
        for (var tmpl : tacletBuilder.goalTemplates()) {
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

    private boolean occurrsOnlyInFindOrRepl(SchemaVariable sv) {
        TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector();
        svc.visit(tacletBuilder.ifSequent());
        for (var tacletGoalTemplate : tacletBuilder.goalTemplates()) {
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

    public ImmutableMap<SchemaVariable, org.key_project.prover.rules.TacletPrefix> getPrefixMap() {
        considerContext();
        return prefixMap;
    }

    public static class InvalidPrefixException extends IllegalStateException {
        private static final long serialVersionUID = 5855187579027274363L;

        InvalidPrefixException(String tacletName, SchemaVariable sv,
                org.key_project.prover.rules.TacletPrefix prefix,
                ImmutableSet<SchemaVariable> sndPrefixVar) {
            super("Schema variable " + sv + "occurs at different places " + "in taclet "
                + tacletName + " with different prefixes.\n" + "Prefix P1:"
                + ((prefix == null) ? DefaultImmutableSet.<SchemaVariable>nil() : prefix)
                + "\n" + "Prefix P2:" + sndPrefixVar);
        }
    }
}
