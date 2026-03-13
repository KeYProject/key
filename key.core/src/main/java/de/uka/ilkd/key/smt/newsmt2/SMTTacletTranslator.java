/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.smt.SMTTranslationException;
import de.uka.ilkd.key.taclettranslation.DefaultTacletTranslator;
import de.uka.ilkd.key.taclettranslation.SkeletonGenerator;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;

/**
 * This class uses the existing taclet translation technology to translate taclets to smt axioms.
 *
 * @author Mattias Ulbrich
 */
public class SMTTacletTranslator {

    private final SkeletonGenerator tacletTranslator = new DefaultTacletTranslator() {
        @Override
        protected JTerm getFindFromTaclet(FindTaclet findTaclet) {
            JTerm org = super.getFindFromTaclet(findTaclet);
            return services.getTermBuilder().label(org, DefinedSymbolsHandler.TRIGGER_LABEL);
        }
    };

    private final Services services;

    public SMTTacletTranslator(Services services) {
        this.services = services;
    }

    public JTerm translate(Taclet taclet) throws SMTTranslationException {

        if (!taclet.getVariableConditions().isEmpty()) {
            throw new SMTTranslationException(
                "Only unconditional taclets without varconds can be used as SMT axioms: "
                    + taclet.name());
        }

        JTerm skeleton = tacletTranslator.translate(taclet, services);

        Map<JOperatorSV, LogicVariable> variables = new HashMap<>();

        skeleton = variablify(skeleton, variables);

        return quantify(skeleton, variables);
    }

    private JTerm quantify(JTerm smt, Map<JOperatorSV, LogicVariable> variables) {
        if (variables.isEmpty()) {
            return smt;
        }

        JTerm[] subs = { smt };
        ImmutableArray<QuantifiableVariable> bvars = new ImmutableArray<>(variables.values());
        return services.getTermFactory().createTerm(Quantifier.ALL, subs, bvars, null);
    }

    private JTerm variablify(JTerm term, Map<JOperatorSV, LogicVariable> variables)
            throws SMTTranslationException {

        Operator op = term.op();
        if (op instanceof JOperatorSV sv) {
            if (!(sv instanceof TermSV || sv instanceof FormulaSV)) {
                throw new SMTTranslationException("Only a few schema variables can be translated. "
                    + "This one cannot. Type " + sv.getClass());
            }
            LogicVariable lv =
                variables.computeIfAbsent(sv, x -> new LogicVariable(x.name(), x.sort()));
            return services.getTermFactory().createTerm(lv);
        }

        JTerm[] subs = new JTerm[term.arity()];
        boolean changes = false;
        for (int i = 0; i < term.arity(); i++) {
            JTerm orgSub = term.sub(i);
            JTerm sub = variablify(orgSub, variables);
            subs[i] = sub;
            if (sub != orgSub) {
                changes = true;
            }
        }

        List<QuantifiableVariable> qvars = new ArrayList<>();
        if (op instanceof Quantifier) {
            for (QuantifiableVariable boundVar : term.boundVars()) {
                if (boundVar instanceof JOperatorSV sv) {
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
            var bvars = new ImmutableArray<>(qvars);
            return services.getTermFactory().createTerm(op, subs, bvars, term.getLabels());
        } else {
            return term;
        }
    }

}
