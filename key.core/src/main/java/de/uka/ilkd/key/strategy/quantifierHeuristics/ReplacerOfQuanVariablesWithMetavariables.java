/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.collection.DefaultImmutableMap;
import org.key_project.util.collection.ImmutableMap;

/**
 * This class is used to create metavariables for every universal variables in quantified formula
 * <code>allTerm</code> and create constant functions for all existential variables. The variables
 * with new created metavariables or constant functions are store to a map <code>mapQM</code>.
 */
@Deprecated
class ReplacerOfQuanVariablesWithMetavariables {

    private ReplacerOfQuanVariablesWithMetavariables() {}

    public static Substitution createSubstitutionForVars(Term allTerm, TermServices services) {
        ImmutableMap<QuantifiableVariable, Term> res =
            DefaultImmutableMap.nilMap();
        Term t = allTerm;
        Operator op = t.op();
        while (op instanceof Quantifier) {
            QuantifiableVariable q = t.varsBoundHere(0).get(0);
            Term m;
            if (op == Quantifier.ALL) {
                Metavariable mv = new Metavariable(ARBITRARY_NAME, q.sort());
                m = services.getTermBuilder().var(mv);
            } else {
                Function f = new Function(ARBITRARY_NAME, q.sort(), new Sort[0]);
                m = services.getTermBuilder().func(f);
            }
            res = res.put(q, m);
            t = t.sub(0);
            op = t.op();
        }
        return new Substitution(res);
    }

    private final static Name ARBITRARY_NAME = new Name("unifier");

}
