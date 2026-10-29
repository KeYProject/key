/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

/**
 * The TermFactory is the <em>only</em> way to create terms using constructors of class Term or any
 * of its subclasses. It is the only class that implements and may exploit knowledge about sub
 * classes of {@link JTerm}. All other classes of the system only know about terms what the
 * {@link JTerm} class offers them.
 *
 * This class is used to encapsulate knowledge about the internal term structures. See
 * {@link TermBuilder} for more convenient methods to create terms.
 */
@SuppressWarnings("deprecation") // term-creation API is bound to the deprecated ImmutableArray
public final class TermFactory {


    private static final ImmutableList<JTerm> NO_SUBTERMS = ImmutableList.of();
    private final Map<JTerm, JTerm> cache;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------


    public TermFactory() {
        this.cache = null;
    }

    public TermFactory(Map<JTerm, JTerm> cache) {
        this.cache = cache;
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------



    /**
     * Master method for term creation. Should be the only place where terms are created in the
     * entire system.
     */
    public JTerm createTerm(@NonNull Operator op, ImmutableList<JTerm> subs,
            ImmutableList<QuantifiableVariable> boundVars,
            ImmutableList<TermLabel> labels) {
        if (op == null) {
            throw new TermCreationException("Given operator is null.");
        }

        if (subs == null || subs.isEmpty()) {
            subs = NO_SUBTERMS;
        }

        return doCreateTerm(op, subs, boundVars, labels, "");
    }

    public JTerm createTerm(Operator op, ImmutableList<JTerm> subs,
            ImmutableList<QuantifiableVariable> boundVars) {

        return createTerm(op, subs, boundVars, null);
    }

    public JTerm createTerm(@NonNull Operator op, JTerm... subs) {
        return createTerm(op, createSubtermArray(subs), null, null);
    }

    public JTerm createTerm(Operator op, JTerm[] subs,
            ImmutableList<QuantifiableVariable> boundVars,
            ImmutableList<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), boundVars, labels);
    }

    public JTerm createTerm(Operator op, JTerm[] subs, TermLabel label) {
        return createTerm(op, subs, null, ImmutableList.ofFixedSize(label));
    }

    public JTerm createTerm(Operator op, JTerm[] subs, ImmutableList<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), null, labels);
    }

    public JTerm createTerm(Operator op, JTerm sub, ImmutableList<TermLabel> labels) {
        return createTerm(op, ImmutableList.ofFixedSize(sub), null, labels);
    }

    public JTerm createTerm(Operator op, JTerm sub1, JTerm sub2,
            ImmutableList<TermLabel> labels) {
        return createTerm(op, new JTerm[] { sub1, sub2 }, labels);
    }


    public JTerm createTerm(Operator op, ImmutableList<TermLabel> labels) {
        return createTerm(op, NO_SUBTERMS, null, labels);
    }

    // -------------------------------------------------------------------------
    // private interface
    // -------------------------------------------------------------------------

    private ImmutableList<JTerm> createSubtermArray(JTerm[] subs) {
        return subs == null || subs.length == 0 ? NO_SUBTERMS : ImmutableList.ofFixedSize(subs);
    }

    private JTerm doCreateTerm(Operator op, ImmutableList<JTerm> subs,
            ImmutableList<QuantifiableVariable> boundVars,
            ImmutableList<TermLabel> labels, String origin) {

        final TermImpl newTerm =
            (labels == null || labels.isEmpty()
                    ? new TermImpl(op, subs, boundVars)
                    : new LabeledTermImpl(op, subs, boundVars, labels, origin));
        // Check if caching is possible. It is not possible if a non-empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (cache != null && !newTerm.containsJavaBlockRecursive()) {
            JTerm term = cache.get(newTerm);
            if (term == null) {
                final JTerm checked = newTerm.checked();
                final JTerm previous = cache.putIfAbsent(checked, checked);
                term = previous != null ? previous : checked;
            }
            return term;
        } else {
            return newTerm.checked();
        }
    }

    /**
     * Reduce the given list of terms into a one term by using the operator. The reduction is
     * left-associative. e.g., the result is {@code ((a op b) op c) op d }.
     *
     * @param junctor the left-associative operator to combine the terms together
     * @param terms a list of non-null temrs
     */
    public @NonNull JTerm createTerm(@NonNull Operator junctor, @NonNull List<JTerm> terms) {
        if (terms.size() == 1) {
            return terms.get(0);
        } else if (terms.size() == 2) {
            return createTerm(junctor, terms.get(0), terms.get(1));
        }
        final Optional<JTerm> reduce = terms.stream().reduce((a, b) -> createTerm(junctor, a, b));
        if (reduce.isPresent()) {
            return reduce.get();
        }
        throw new IllegalArgumentException("list of terms is empty.");
    }

    public JTerm createTermWithOrigin(JTerm t, String origin) {
        return doCreateTerm(t.op(), t.subs(), t.boundVars(), t.getLabels(), origin);
    }
}
