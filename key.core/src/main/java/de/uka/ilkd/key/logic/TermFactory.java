/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import de.uka.ilkd.key.logic.label.TermLabel;

import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.util.collection.ImmutableArray;

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
public final class TermFactory {


    private static final ImmutableArray<JTerm> NO_SUBTERMS = new ImmutableArray<>();
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
    public JTerm createTerm(@NonNull Operator op, ImmutableArray<JTerm> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            ImmutableArray<TermLabel> labels) {
        if (op == null) {
            throw new TermCreationException("Given operator is null.");
        }

        if (subs == null || subs.isEmpty()) {
            subs = NO_SUBTERMS;
        }

        return doCreateTerm(op, subs, boundVars, labels, "");
    }

    public JTerm createTerm(Operator op, ImmutableArray<JTerm> subs,
            ImmutableArray<QuantifiableVariable> boundVars) {

        return createTerm(op, subs, boundVars, null);
    }

    public JTerm createTerm(@NonNull Operator op, JTerm... subs) {
        return createTerm(op, createSubtermArray(subs), null, null);
    }

    public JTerm createTerm(Operator op, JTerm[] subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            ImmutableArray<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), boundVars, labels);
    }

    public JTerm createTerm(Operator op, JTerm[] subs, TermLabel label) {
        return createTerm(op, subs, null, new ImmutableArray<>(label));
    }

    public JTerm createTerm(Operator op, JTerm[] subs, ImmutableArray<TermLabel> labels) {
        return createTerm(op, createSubtermArray(subs), null, labels);
    }

    public JTerm createTerm(Operator op, JTerm sub, ImmutableArray<TermLabel> labels) {
        return createTerm(op, new ImmutableArray<>(sub), null, labels);
    }

    public JTerm createTerm(Operator op, JTerm sub1, JTerm sub2,
            ImmutableArray<TermLabel> labels) {
        return createTerm(op, new JTerm[] { sub1, sub2 }, labels);
    }


    public JTerm createTerm(Operator op, ImmutableArray<TermLabel> labels) {
        return createTerm(op, NO_SUBTERMS, null, labels);
    }

    // -------------------------------------------------------------------------
    // private interface
    // -------------------------------------------------------------------------

    private ImmutableArray<JTerm> createSubtermArray(JTerm[] subs) {
        return subs == null || subs.length == 0 ? NO_SUBTERMS : new ImmutableArray<>(subs);
    }

    private JTerm doCreateTerm(Operator op, ImmutableArray<JTerm> subs,
            ImmutableArray<QuantifiableVariable> boundVars,
            ImmutableArray<TermLabel> labels, String origin) {

        final TermImpl newTerm =
            (labels == null || labels.isEmpty()
                    ? new TermImpl(op, subs, boundVars, origin)
                    : new LabeledTermImpl(op, subs, boundVars, labels, origin));
        // Check if caching is possible. It is not possible if a non-empty JavaBlock is available
        // in the term or in one of its children because the meta information like PositionInfos
        // may be different.
        if (cache != null && !newTerm.containsJavaBlockRecursive()) {
            JTerm term;
            synchronized (cache) {
                term = cache.get(newTerm);
            }
            if (term == null) {
                term = newTerm.checked();
                synchronized (cache) {
                    cache.put(term, term);
                }
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
