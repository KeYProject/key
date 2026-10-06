/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;

import org.key_project.logic.Term;
import org.key_project.util.collection.ImmutableSet;

public interface Trigger {
    /**
     * @param targetTerm
     * @param services
     * @return all substitution that found from the targeTerm by matching this trigger to targeTerm.
     */
    ImmutableSet<Substitution> getSubstitutionsFromTerms(
            ImmutableSet<Term> targetTerm, Services services);

    /**
     * As above, and where {@code basicMatching} is set a theory-provided trigger is matched by
     * {@link BasicMatching} as well as unified. Only that matching lets a theory solve a
     * array index, and only it binds a metavariable to a term the trigger never read.
     *
     * @param targetTerm the terms to match against
     * @param services access to the theory's operators
     * @param basicMatching whether a theory-provided trigger is also matched by
     *        {@link BasicMatching}
     * @return the substitutions found
     */
    default ImmutableSet<Substitution> getSubstitutionsFromTerms(ImmutableSet<Term> targetTerm,
            Services services, boolean basicMatching) {
        return getSubstitutionsFromTerms(targetTerm, services);
    }

    Term getTriggerTerm();

    /**
     * Whether this trigger is a theory's generalization of another one rather than a term of the
     * formula itself.
     *
     * @return whether the trigger was derived
     */
    default boolean isTheoryProvided() {
        return false;
    }

    /**
     * Whether this trigger is a theory's fallback for a clause without a covering trigger.
     * Instances it yields carry the {@code FALLBACK} origin.
     *
     * @return whether the trigger is a fallback
     */
    default boolean isFallback() {
        return false;
    }
}
