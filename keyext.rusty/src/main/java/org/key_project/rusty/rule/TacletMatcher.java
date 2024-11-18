/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.prover.rules.AssumesFormulaInstantiation;
import org.key_project.prover.rules.AssumesMatchResult;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.logic.op.sv.SchemaVariable;


public interface TacletMatcher extends org.key_project.prover.rules.TacletMatcher {
    /**
     * matches the given term against the taclet's find term if the taclet has no find term or the
     * match is unsuccessful <code>null</code>
     * is returned
     *
     * @param term the Term to be matched against the find expression
     *        of the taclet
     * @param matchCond the MatchConditions with side conditions to be
     *        satisfied, e.g. partial instantiations of schema variables; before
     *        calling this method the constraint contained in the match conditions
     *        must be ensured to be satisfiable, i.e.
     *        {@code matchCond.getConstraint().isSatisfiable()} must return true
     *
     * @param services the Services
     * @return the found schema variable mapping or <code>null</code> if the matching failed
     */
    MatchConditions matchFind(Term term, MatchConditions matchCond,
            Services services);

    @Override
    default MatchConditions matchFind(Term term,
            org.key_project.prover.rules.MatchConditions matchCond, LogicServices services) {
        return matchFind(term, (MatchConditions) matchCond, (Services) services);
    }

    /**
     * checks if the conditions for a correct instantiation are satisfied
     *
     * @param var the SchemaVariable to be instantiated
     * @param instantiationCandidate the SVSubstitute, which is a candidate for a possible
     *        instantiation of var
     * @param matchCond the MatchConditions which have to be respected for the new match
     * @param services the Services object encapsulating information about the Rust type model
     * @return the match conditions resulting from matching <code>var</code> with
     *         <code>instantiationCandidate</code> or <code>null</code> if a match was not possible
     */
    MatchConditions checkVariableConditions(SchemaVariable var,
            SyntaxElement instantiationCandidate, MatchConditions matchCond, Services services);

    @Override
    default MatchConditions checkVariableConditions(org.key_project.logic.op.sv.SchemaVariable var,
            SyntaxElement instantiationCandidate,
            org.key_project.prover.rules.MatchConditions matchCond, LogicServices services) {
        return checkVariableConditions((SchemaVariable) var, instantiationCandidate,
            (MatchConditions) matchCond, (Services) services);
    }

    /**
     * checks the provided matches against the variable conditions of this taclet It returns the
     * resulting match conditions or <code>null</code> if the found matches do not satisfy the
     * variable conditions. If the given matchconditions are <code>null</code> then
     * <code>null</code> is returned
     *
     * @param matchConditions the matches to be checked
     * @param services the {@link Services}
     * @return the resulting match conditions or <code>null</code> if given matches do not satisfy
     *         the taclet's variable conditions
     */
    MatchConditions checkConditions(MatchConditions matchConditions, Services services);

    @Override
    default MatchConditions checkConditions(
            org.key_project.prover.rules.MatchConditions matchConditions, LogicServices services) {
        return checkConditions((MatchConditions) matchConditions, (Services) services);
    }

    /**
     * Match the given template (which is probably a formula of the assumes-sequent) against a list
     * of
     * constraint formulas (probably the formulas of the antecedent or the succedent), starting with
     * the given instantiations and constraint {@code p_matchCond}.
     *
     * @param toMatch list of constraint formulas to match p_template to
     * @param template template formula as in "match"
     * @param matchCond already performed instantiations
     * @param services the Services object encapsulating information about the Rust datastructures
     *        like (static)types etc.
     * @return Two lists (in an {@link IfMatchResult} object), containing the elements of
     *         {@code p_toMatch} that
     *         could successfully be matched against p_template, and the corresponding
     *         MatchConditions.
     */
    AssumesMatchResult matchAssumes(Iterable<AssumesFormulaInstantiation> toMatch, Term template,
            MatchConditions matchCond, Services services);

    default AssumesMatchResult matchAssumes(Iterable<AssumesFormulaInstantiation> toMatch,
            Term template,
            org.key_project.prover.rules.MatchConditions matchCond, LogicServices services) {
        return matchAssumes(toMatch, template, (MatchConditions) matchCond, (Services) services);
    }

    /**
     * Match the whole if sequent using the given list of instantiations of all assumes-sequent
     * formulas,
     * starting with the instantiations given by p_matchCond.
     * <p>
     * PRECONDITION: {@code p_toMatch.size () == ifSequent().size()}
     * </p>
     *
     * @return resulting MatchConditions or null if the given list p_toMatch does not match
     */
    MatchConditions matchAssumes(Iterable<AssumesFormulaInstantiation> toMatch,
            MatchConditions matchCond, Services services);

    default MatchConditions matchAssumes(Iterable<AssumesFormulaInstantiation> toMatch,
            org.key_project.prover.rules.MatchConditions matchCond, LogicServices services) {
        return matchAssumes(toMatch, (MatchConditions) matchCond, (Services) services);
    }

    MatchConditions matchSV(SchemaVariable sv, Term term, MatchConditions matchConditions,
            Services services);

    default MatchConditions matchSV(org.key_project.logic.op.sv.SchemaVariable sv, Term term,
            org.key_project.prover.rules.MatchConditions matchConditions,
            LogicServices services) {
        return matchSV((SchemaVariable) sv, term, (MatchConditions) matchConditions,
            (Services) services);
    }

    MatchConditions matchSV(SchemaVariable sv, RustyProgramElement pe,
            MatchConditions matchConditions, Services services);
}
