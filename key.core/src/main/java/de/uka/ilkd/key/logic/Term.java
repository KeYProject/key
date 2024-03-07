/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.equality.TermEqualsModProperty;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;

import org.key_project.logic.Name;
import org.key_project.logic.Visitor;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/**
 * In contrast to the distinction of formulas and terms as made by most of the inductive definitions
 * of the syntax of a logic, an instance of this class can stand for a term or a formula. This is
 * done for implementation reasons, as their structure is quite similar and there are good reasons
 * concerning the software's design/architecture (for example using same visitors, reduction of case
 * distinction, unified interfaces etc.). However, they are strictly separated by their sorts. A
 * formula (and just a formula) must have the sort {@link JavaDLTheory#FORMULA}. Terms of a
 * different sort
 * are terms in the customary logic sense. A term of sort formula is allowed exact there, where a
 * formula in logic is allowed to appear, same for terms of different sorts. Some words about other
 * design decisions:
 * <ol>
 * <li>terms are immutable, this means after a term object is created, it cannot be changed. The
 * advantage is that we can use term sharing and saving a lot of memory space.</li>
 * <li>Term has to be created using the {@link TermFactory} and _not_ by using the constructors
 * itself.</li>
 * <li>Term is subclassed, but all subclasses have to be package private, so that all other classes
 * except {@link TermFactory} know only the class Term and its interface. Even most classes of the
 * logic package.</li>
 * <li>as it is immutable, most (all) attributes should be declared final</li>
 * </ol>
 * Term supports the {@link Visitor} pattern. Two different visit strategies are currently
 * supported: {@link Term#execPostOrder(Visitor)} and {@link Term#execPreOrder(Visitor)}.
 */
public interface Term
        extends SVSubstitute, Sorted, TermEqualsModProperty, org.key_project.logic.Term {
    @Override
    Operator op();

    /**
     * The subterms.
     */
    @Override
    ImmutableArray<Term> subs();

    /**
     * {@inheritDoc}
     */
    @Override
    Term sub(int n);

    /**
     * {@inheritDoc}
     */
    @Override
    ImmutableArray<QuantifiableVariable> boundVars();

    /**
     * {@inheritDoc}
     */
    @Override
    ImmutableArray<QuantifiableVariable> varsBoundHere(int n);

    /**
     * {@inheritDoc}
     */
    @Override
    ImmutableSet<QuantifiableVariable> freeVars();

    /**
     * The Java block at top level.
     */
    @NonNull
    JavaBlock javaBlock();

    /**
     * returns true if the term is labeled
     */
    boolean hasLabels();

    /**
     * checks if the given label is attached to the term
     *
     * @param label the TermLabel for which to look (must not be null)
     */
    boolean containsLabel(TermLabel label);

    /**
     * returns list of labels attached to this term
     *
     * @return list of labels (maybe be empty but never <code>null</code>
     */
    ImmutableArray<TermLabel> getLabels();

    /**
     * Returns the first {@link TermLabel} with the given {@link Name}.
     *
     * @param termLabelName The {@link Name} of the {@link TermLabel} to search.
     * @return The first found {@link TermLabel} or {@code null} if not available.
     */
    TermLabel getLabel(Name termLabelName);

    /**
     * Checks if the {@link Term} or one of its direct or indirect children contains a non-empty
     * {@link JavaBlock}.
     *
     * @return {@code true} The {@link Term} or one of its direct or indirect children contains a
     *         non-empty {@link JavaBlock}, {@code false} no {@link JavaBlock} available.
     */
    boolean containsJavaBlockRecursive();

    /**
     * Returns a human-readable source of this term. For example the filename with line and offset.
     */
    default @Nullable String getOrigin() { return null; }
}
