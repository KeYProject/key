/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.util.Pair;

import org.key_project.util.collection.ImmutableSet;


/**
 * An axiom originating from a (JML) specification, belonging to a particular class, and
 * constraining a particular observer symbol. A class axiom always has an associated visibility. The
 * visibility determines in which proofs the axiom is available, in accordance with the visibility
 * rules of Java. If visible, it is made available not as a formula, but as one or many taclets (for
 * performance reasons).
 */
public abstract class ClassAxiom implements SpecificationElement {
    protected String displayName;

    /**
     * Returns the axiomatised function symbol.
     */
    public abstract IObserverFunction getTarget();


    /**
     * Returns the pairs (kjt, obs) for which there is an occurrence of o.obs in the axiom, where
     * kjt is the type of o (excluding the defining occurrence of the axiom target).
     */
    public abstract ImmutableSet<Pair<Sort, IObserverFunction>> getUsedObservers(Services services);

    /**
     * The axiom as one or many taclets, where the non-defining occurrences of the passed observers
     * are replaced by their "limited" counterparts.
     */
    public abstract ImmutableSet<Taclet> getTaclets(
            ImmutableSet<Pair<Sort, IObserverFunction>> toLimit, Services services);

    @Override
    public String getDisplayName() {
        return displayName == null ? getName() : displayName;
    }
}
