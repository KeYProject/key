/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.tacletbuilder;

import java.util.Iterator;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.*;

import org.key_project.util.collection.*;

public class TacletPrefixBuilder {

    /**
     * set of all schemavariables that are only allowed to be matched with quantifiable variables.
     */
    private ImmutableSet<SchemaVariable> currentlyBoundVars =
        DefaultImmutableSet.nil();
    private final TacletBuilder<? extends Taclet> tacletBuilder;

    protected ImmutableMap<SchemaVariable, TacletPrefix> prefixMap =
        DefaultImmutableMap.nilMap();

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

    private void setPrefixOfOccurrence(SchemaVariable sv,
            ImmutableSet<SchemaVariable> relevantBoundVars) {
        prefixMap = prefixMap.put(sv, new TacletPrefix(relevantBoundVars, false));
    }

    /**
     * removes all variables x that are declared as x not free in sv from the currently bound vars
     * set.
     */
    private ImmutableSet<SchemaVariable> removeNotFreeIn(SchemaVariable sv) {
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

    private void visit(Term t) {
        if (t.op() instanceof Modality mod && mod.kind() instanceof ModalOperatorSV msv) {
            // TODO: Is false correct?
            prefixMap.put(msv, new TacletPrefix(ImmutableSet.empty(), false));
        }
        if (t.op() instanceof SchemaVariable && t.arity() == 0 && !(t.op() instanceof VariableSV)
                && !(t.op() instanceof ProgramSV) && !(t.op() instanceof SkolemTermSV)) {
            SchemaVariable sv = (SchemaVariable) t.op();
            ImmutableSet<SchemaVariable> relevantBoundVars = removeNotFreeIn(sv);
            TacletPrefix prefix = prefixMap.get(sv);
            if (prefix == null || prefix.prefix().equals(relevantBoundVars)) {
                setPrefixOfOccurrence(sv, relevantBoundVars);
            } else {
                throw new InvalidPrefixException(tacletBuilder.getName().toString(), sv, prefix,
                    relevantBoundVars);
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
                    TacletPrefix prefix = prefixMap.get(sv);
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
            visit(cf.formula());
        }
    }

    private void visit(TacletGoalTemplate templ) {
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

            if (addRulePrefix != null && !addRulePrefix.prefix().equals(entry.value().prefix())) {
                throw new InvalidPrefixException(tacletBuilder.getName().toString(), entry.key(),
                    entry.value(), addRulePrefix.prefix());
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
        @SuppressWarnings("unchecked")
        RewriteTacletBuilder<? extends RewriteTaclet> rwtacletBuilder =
            (RewriteTacletBuilder<? extends RewriteTaclet>) tacletBuilder;
        int count = 0;
        for (TacletGoalTemplate tmpl : rwtacletBuilder.goalTemplates()) {
            if (tmpl instanceof RewriteTacletGoalTemplate) {
                if (((RewriteTacletGoalTemplate) tmpl).replaceWith() != null) {
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
        @SuppressWarnings("unchecked")
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
                ImmutableSet<SchemaVariable> sndPrefixVar) {
            super("Schema variable " + sv + "occurs at different places " + "in taclet "
                + tacletName + " with different prefixes.\n" + "Prefix P1:"
                + ((prefix == null) ? DefaultImmutableSet.<SchemaVariable>nil() : prefix.prefix())
                + "\n" + "Prefix P2:" + sndPrefixVar);
        }

    }

}
