/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * A property that can be used in
 * {@link TermEqualsModProperty#equalsModProperty(Object, TermProperty)}.
 * Renaming of variables is ignored in this equality check.
 */
public class RenamingTermProperty implements TermProperty {
    /**
     * The single instance of this property.
     */
    public static final RenamingTermProperty RENAMING_TERM_PROPERTY = new RenamingTermProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed
     * through {@link RenamingTermProperty#RENAMING_TERM_PROPERTY} and is used as a parameter for
     * {@link TermProperty#equalsModThisProperty(Term, Object)}.
     */
    private RenamingTermProperty() {}

    /**
     * Checks if {@code o} is a term syntactically equal to {@code term} modulo bound renaming.
     *
     * @param term a term
     * @param o the object compared to {@code term}
     * @return true iff {@code o} has the same values in operator, sort, arity, varsBoundHere
     *         and javaBlock as {@code term} modulo bound renaming
     */
    @Override
    public Boolean equalsModThisProperty(Term term, Object o) {
        if (o == term) {
            return true;
        }
        if (!(o instanceof Term t)) {
            return false;
        }
        return unifyHelp(term, t, ImmutableSLList.nil(),
            ImmutableSLList.nil(), null);
    }

    @Override
    public int hashCodeModThisProperty(Term term) {
        throw new UnsupportedOperationException(
            "Hashing of terms modulo renaming not yet implemented!");
    }

    // equals modulo renaming logic

    /**
     * Compare two quantifiable variables if they are equal modulo renaming.
     *
     * @param ownVar first QuantifiableVariable to be compared
     * @param cmpVar second QuantifiableVariable to be compared
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     */
    private static boolean compareBoundVariables(QuantifiableVariable ownVar,
            QuantifiableVariable cmpVar, ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars) {

        final int ownNum = indexOf(ownVar, ownBoundVars);
        final int cmpNum = indexOf(cmpVar, cmpBoundVars);

        if (ownNum == -1 && cmpNum == -1) {
            // if both variables are not bound the variables have to be the
            // same object
            return ownVar == cmpVar;
        }

        // otherwise the variables have to be bound at the same point (and both
        // be bound)
        return ownNum == cmpNum;
    }

    /**
     * @return the index of the first occurrence of <code>var</code> in <code>list</code>, or
     *         <code>-1</code> if the variable is not an element of the list
     */
    private static int indexOf(QuantifiableVariable var, ImmutableList<QuantifiableVariable> list) {
        int res = 0;
        while (!list.isEmpty()) {
            if (list.head() == var) {
                return res;
            }
            ++res;
            list = list.tail();
        }
        return -1;
    }

    /**
     * Compares two terms modulo bound renaming.
     *
     * @param t0 the first term
     * @param t1 the second term
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     * @return <code>true</code> is returned iff the terms are equal modulo bound renaming
     */
    private boolean unifyHelp(Term t0, Term t1, ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars, NameAbstractionTable nat) {

        if (t0 == t1 && ownBoundVars.equals(cmpBoundVars)) {
            return true;
        }

        final Operator op0 = t0.op();

        if (op0 instanceof QuantifiableVariable) {
            return handleQuantifiableVariable(t0, t1, ownBoundVars, cmpBoundVars);
        }

        final Operator op1 = t1.op();

        if (!(op0 instanceof ProgramVariable) && op0 != op1) {
            return false;
        }

        if (t0.sort() != t1.sort() || t0.arity() != t1.arity()) {
            return false;
        }

        nat = handleJava(t0, t1, nat);
        if (nat == FAILED) {
            return false;
        }

        return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    private boolean handleQuantifiableVariable(Term t0, Term t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars) {
        return (t1.op() instanceof QuantifiableVariable)
                && compareBoundVariables((QuantifiableVariable) t0.op(),
                    (QuantifiableVariable) t1.op(), ownBoundVars, cmpBoundVars);
    }

    /**
     * used to encode that <tt>handleJava</tt> results in an unsatisfiable constraint (faster than
     * using exceptions)
     */
    private static final NameAbstractionTable FAILED = new NameAbstractionTable();

    private static NameAbstractionTable handleJava(Term t0, Term t1, NameAbstractionTable nat) {

        if (!t0.javaBlock().isEmpty() || !t1.javaBlock().isEmpty()) {
            nat = checkNat(nat);
            if (!t0.javaBlock().equalsModRenaming(t1.javaBlock(), nat)) {
                return FAILED;
            }
        }

        if (!(t0.op() instanceof SchemaVariable) && t0.op() instanceof ProgramVariable) {
            if (!(t1.op() instanceof ProgramVariable)) {
                return FAILED;
            }
            nat = checkNat(nat);
            if (!((ProgramVariable) t0.op()).equalsModRenaming((ProgramVariable) t1.op(), nat)) {
                return FAILED;
            }
        }

        return nat;
    }

    private boolean descendRecursively(Term t0, Term t1,
            ImmutableList<QuantifiableVariable> ownBoundVars,
            ImmutableList<QuantifiableVariable> cmpBoundVars, NameAbstractionTable nat) {

        for (int i = 0; i < t0.arity(); i++) {
            ImmutableList<QuantifiableVariable> subOwnBoundVars = ownBoundVars;
            ImmutableList<QuantifiableVariable> subCmpBoundVars = cmpBoundVars;

            if (t0.varsBoundHere(i).size() != t1.varsBoundHere(i).size()) {
                return false;
            }
            for (int j = 0; j < t0.varsBoundHere(i).size(); j++) {
                final QuantifiableVariable ownVar = t0.varsBoundHere(i).get(j);
                final QuantifiableVariable cmpVar = t1.varsBoundHere(i).get(j);
                if (ownVar.sort() != cmpVar.sort()) {
                    return false;
                }

                subOwnBoundVars = subOwnBoundVars.prepend(ownVar);
                subCmpBoundVars = subCmpBoundVars.prepend(cmpVar);
            }

            boolean newConstraint =
                unifyHelp(t0.sub(i), t1.sub(i), subOwnBoundVars, subCmpBoundVars, nat);

            if (!newConstraint) {
                return false;
            }
        }

        return true;
    }

    private static NameAbstractionTable checkNat(NameAbstractionTable nat) {
        if (nat == null) {
            return new NameAbstractionTable();
        }
        return nat;
    }
    // end of equals modulo renaming logic

}
