/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableSet;

public interface Trigger {

    /**
     * @param targetTerm
     * @param services
     * @return all substitution that found from the targeTerm by matching
     *         this trigger to targeTerm.
     */
    public abstract ImmutableSet<Substitution> getSubstitutionsFromTerms(
            ImmutableSet<Term> targetTerm,
            Services services);

    public abstract Term getTriggerTerm();
}
