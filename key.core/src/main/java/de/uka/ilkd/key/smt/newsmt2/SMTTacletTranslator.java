/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.taclettranslation.DefaultTacletTranslator;
import de.uka.ilkd.key.taclettranslation.SkeletonGenerator;

import org.key_project.util.collection.ImmutableArray;

/**
 * This class uses the existing taclet translation technology to translate taclets to smt axioms.
 *
 * @author Mattias Ulbrich
 */
public class SMTTacletTranslator {

    private final SkeletonGenerator tacletTranslator = new DefaultTacletTranslator() {
        @Override
        protected Term getFindFromTaclet(FindTaclet findTaclet) {
            Term org = super.getFindFromTaclet(findTaclet);
            return services.getTermBuilder().label(org, DefinedSymbolsHandler.TRIGGER_LABEL);
        }
    };

    private final Services services;

    public SMTTacletTranslator(Services services) {
        this.services = services;
    }

    public Term translate(Taclet taclet) throws SMTTranslationException {

        if (!taclet.getVariableConditions().isEmpty()) {
            throw new SMTTranslationException(
                "Only unconditional taclets without varconds can be used as SMT axioms: "
                    + taclet.name());
        }

        Term skeleton = tacletTranslator.translate(taclet, services);

        Map<SchemaVariable, LogicVariable> variables = new HashMap<>();

        skeleton = variablify(skeleton, variables);

        return quantify(skeleton, variables);
    }

    private Term quantify(Term smt, Map<SchemaVariable, LogicVariable> variables)
            throws SMTTranslationException {

        if (variables.isEmpty()) {
            return smt;
        }

        Term[] subs = { smt };
        ImmutableArray<QuantifiableVariable> bvars = new ImmutableArray<>(variables.values());
        return services.getTermFactory().createTerm(Quantifier.ALL, subs, bvars, null);
    }

    private Term variablify(Term term, Map<SchemaVariable, LogicVariable> variables)
            throws SMTTranslationException {

        Operator op = term.op();
        if (op instanceof SchemaVariable) {
            SchemaVariable sv = (SchemaVariable) op;
            if (!(sv instanceof TermSV || sv instanceof FormulaSV)) {
                throw new SMTTranslationException("Only a few schema variables can be translated. "
                    + "This one cannot. Type " + sv.getClass());
            }
            LogicVariable lv =
                variables.computeIfAbsent(sv, x -> new LogicVariable(x.name(), x.sort()));
            return services.getTermFactory().createTerm(lv);
        }

        Term[] subs = new Term[term.arity()];
        boolean changes = false;
        for (int i = 0; i < term.arity(); i++) {
            Term orgSub = term.sub(i);
            Term sub = variablify(orgSub, variables);
            subs[i] = sub;
            if (sub != orgSub) {
                changes = true;
            }
        }

        List<QuantifiableVariable> qvars = new ArrayList<>();
        if (op instanceof Quantifier) {
            Quantifier q = (Quantifier) op;
            for (QuantifiableVariable boundVar : term.boundVars()) {
                if (boundVar instanceof SchemaVariable) {
                    SchemaVariable sv = (SchemaVariable) boundVar;
                    LogicVariable lv =
                        variables.computeIfAbsent(sv, x -> new LogicVariable(x.name(), x.sort()));
                    qvars.add(lv);
                    changes = true;
                } else {
                    qvars.add(boundVar);
                }
            }
        }

        if (changes) {
            ImmutableArray bvars = new ImmutableArray(qvars);
            return services.getTermFactory().createTerm(op, subs, bvars, null, term.getLabels());
        } else {
            return term;
        }
    }

}
