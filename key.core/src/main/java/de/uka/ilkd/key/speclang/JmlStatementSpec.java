/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.statement.JmlAssert;
import de.uka.ilkd.key.java.ast.statement.SetStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;

import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * This record represents information which are necessary to evaluate JML statements.
 * JML statements need to maintain the current variable set as well as the updated information
 * for the KeY terms
 * they describe. This record represents this information, i.e., the scope of variables, and a
 * list of terms, in
 * an immutable fasion. Updates require to create instances.
 * <p>
 * <b>Note:</b> There is an immutability hole in {@link ProgramVariableCollection} due to
 * mutable
 * {@link Map}
 * <p>
 * For {@link JmlAssert} this is the formula behind the
 * assert
 * (Potientially also containing the formulas within the optional proof).
 * For {@link SetStatement} this is the target and the value
 * terms.
 * You may want to use the index constant for accessing them:
 * {@link SetStatement#INDEX_TARGET},
 * {@link SetStatement#INDEX_VALUE},
 * {@link JmlAssert#INDEX_CONDITION}
 *
 * @param vars
 * @param terms
 */
public record JmlStatementSpec(
        ProgramVariableCollection vars,
        ImmutableList<JTerm> terms) {
    /**
     * Retrieve a term
     *
     * @param index a index to the list of {@code terms}.
     * @return the term at {@code index} in the {@code terms} list
     * @throws IndexOutOfBoundsException if the given {@code index} is negative or
     *         {@code >= terms().size()}
     */
    public JTerm term(int index) {
        return terms.get(index);
    }

    /**
     * Retrieve a term with an update to the given {@code self} term.
     *
     * @param services the corresponding services instance
     * @param self a term which describes the {@code self} object aka. this on the current
     *        sequence
     * @param index the index of the term in {@code terms()}
     * @return a term updated with {@code self} and the {@code vars()}.
     */
    public JTerm getTerm(Services services, @Nullable JTerm self, int index) {
        var term = term(index);

        final TermFactory termFactory = services.getTermFactory();
        final TermReplacementMap replacementMap = new TermReplacementMap(termFactory);
        if (self != null) {
            replacementMap.replaceSelf(vars().selfVar, self, services);
        }
        replacementMap.replaceRemembranceLocalVariables(vars().atPreVars, vars().atPres,
            services);
        replacementMap.replaceRemembranceLocalVariables(vars().atBeforeVars, vars().atBefores,
            services);
        final OpReplacer replacer =
            new OpReplacer(replacementMap, termFactory, services.getProof());
        return replacer.replace(term);
    }

    /**
     * Updates the variables given the new {@code atPres} (variable in pre state) map and the
     * services.
     * The update is applied directly and an updated specification is returned. You need to
     * attach the updated spec to the statement node by yourself.
     *
     * @param atPres a non-null map of a map of program variable to a term which describes
     *        the value of this variable in the pre-state.
     * @param services the corresponding services object
     * @return a fresh {@link JmlStatementSpec} instance, non-registered.
     */
    public JmlStatementSpec updateVariables(Map<LocationVariable, JTerm> atPres,
            Services services) {
        var termFactory = services.getTermFactory();
        var replacementMap = new TermReplacementMap(termFactory);
        replacementMap.replaceRemembranceLocalVariables(vars.atPreVars, atPres, services);
        var replacer = new OpReplacer(replacementMap, termFactory, services.getProof());
        var newTerms = terms().map(replacer::replace);
        return new JmlStatementSpec(
            new ProgramVariableCollection(vars.selfVar, vars.paramVars, vars.resultVar,
                vars.excVar,
                vars.atPreVars, atPres, vars.atBeforeVars, vars.atBefores),
            newTerms);
    }
}
