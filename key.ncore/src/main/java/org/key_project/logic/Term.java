/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.logic;

import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSet;

/**
 * This interface is implemented by classes that represent terms or formulas.
 */
public interface Term extends LogicElement, Sorted {
    /**
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f").
     */
    Operator op();

    /**
     * The top operator (e.g., in "A and B" this is "and", in f(x,y) it is "f") cast to the passed
     * type.
     */
    <T> T op(Class<T> opClass) throws IllegalArgumentException;

    /**
     * The subterms.
     */
    ImmutableArray<? extends Term> subs();

    /**
     * The <code>n</code>-th direct subterm.
     */
    Term sub(int n);

    /**
     * The logical variables bound by the top level operator.
     */
    ImmutableArray<? extends QuantifiableVariable> boundVars();

    /**
     * The logical variables bound by the top level operator for the nth subterm.
     */
    ImmutableArray<? extends QuantifiableVariable> varsBoundHere(int n);

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
    ImmutableSet<? extends QuantifiableVariable> freeVars();

    /**
     * Returns a serial number for a term. The serial number is not persistent.
     */
    int serialNumber();

    /**
     * The visitor is handed through till the bottom of the tree, and then it walks upwards, while
     * at
     * each upstep the method visit of the visitor is called.
     *
     * @param visitor the Visitor
     */
    <T extends Term> void execPostOrder(Visitor<T> visitor);

    /**
     * The visitor walks downwards the tree, while at each downstep the method visit of the visitor
     * is called.
     *
     * @param visitor the Visitor
     */
    <T extends Term> void execPreOrder(Visitor<T> visitor);
}
