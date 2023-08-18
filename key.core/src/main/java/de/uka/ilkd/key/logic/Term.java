/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import javax.annotation.Nullable;

import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.sort.Sort;

import org.key_project.util.EqualsModProofIrrelevancy;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

/**
 * In contrast to the distinction of formulas and terms as made by most of the inductive definitions
 * of the syntax of a logic, an instance of this class can stand for a term or a formula. This is
 * done for implementation reasons, as their structure is quite similar and there are good reasons
 * concerning the software's design/architecture (for example using same visitors, reduction of case
 * distinction, unified interfaces etc.). However, they are strictly separated by their sorts. A
 * formula (and just a formula) must have the sort {@link Sort#FORMULA}. Terms of a different sort
 * are terms in the customary logic sense. A term of sort formula is allowed exact there, where a
 * formuala in logic is allowed to appear, same for terms of different sorts. Some words about other
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
public interface Term extends SVSubstitute, Sorted, EqualsModProofIrrelevancy {

    /**
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f").
     */
    Operator op();

    /**
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f") casted to the passed
     * type.
     */
    <T> T op(Class<T> opClass) throws IllegalArgumentException;

    /**
     * The subterms.
     */
    ImmutableArray<Term> subs();

    /**
     * The <code>n</code>-th direct subterm.
     */
    Term sub(int n);

    /**
     * The logical variables bound by the top level operator.
     */
    ImmutableArray<QuantifiableVariable> boundVars();

    /**
     * The logical variables bound by the top level operator for the nth subterm.
     */
    ImmutableArray<QuantifiableVariable> varsBoundHere(int n);

    /**
     * The Java block at top level.
     */
    JavaBlock javaBlock();

    /**
     * The arity of the term.
     */
    int arity();

    /**
     * The sort of the term.
     */
    @Override
    Sort sort();

    /**
     * The nesting depth of this term.
     */
    int depth();

    /**
     * Whether all operators in this term are rigid.
     */
    boolean isRigid();

    /**
     * The set of free quantifiable variables occurring in this term.
     */
    ImmutableSet<QuantifiableVariable> freeVars();

    /**
     * The visitor is handed through till the bottom of the tree and then it walks upwards, while at
     * each upstep the method visit of the visitor is called.
     *
     * @param visitor the Visitor
     */
    void execPostOrder(Visitor visitor);

    /**
     * The visitor walks downwards the tree, while at each downstep the method visit of the visitor
     * is called.
     *
     * @param visitor the Visitor
     */
    void execPreOrder(Visitor visitor);

    /**
     * Compares if two terms are equal modulo bound renaming
     *
     * @param o another term,
     * @return true iff the given term has the same values in operator, sort, arity, varsBoundHere
     *         and javaBlock as this object modulo bound renaming
     */
    boolean equalsModRenaming(Term o);

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
     * Returns a serial number for a term. The serial number is not persistent.
     */
    int serialNumber();


    /**
     * Checks if the {@link Term} or one of its direct or indirect children contains a non empty
     * {@link JavaBlock}.
     *
     * @return {@code true} The {@link Term} or one of its direct or indirect children contains a
     *         non empty {@link JavaBlock}, {@code false} no {@link JavaBlock} available.
     */
    boolean containsJavaBlockRecursive();

    /**
     * Checks if {@code o} is a term syntactically equal to this one, except for some irrelevant
     * labels.
     *
     * @param o an object
     * @return {@code true} iff {@code o} is a term syntactically equal to this one, except for
     *         their labels.
     * @see TermLabel#isProofRelevant() isStrategyRelevant
     */
    boolean equalsModIrrelevantTermLabels(Object o);

    /**
     * Checks if {@code o} is a term syntactically equal to this one, ignoring <b>all</b> term
     * labels.
     *
     * @param o an object
     * @return {@code true} iff {@code o} is a term syntactically equal to this ignoring term labels
     */
    boolean equalsModTermLabels(Object o);

    /**
     * Returns an human-readable source of this term. For example the filename with line and offset.
     */
    default @Nullable String getOrigin() { return null; }
}
