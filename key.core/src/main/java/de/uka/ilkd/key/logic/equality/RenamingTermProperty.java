/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.equality;

import de.uka.ilkd.key.java.JavaProgramElement;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import static de.uka.ilkd.key.logic.equality.RenamingSourceElementProperty.RENAMING_SOURCE_ELEMENT_PROPERTY;

/**
 * A property that can be used in
 * {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])} for terms.
 * Renaming of variables is ignored in this equality check.
 * <p>
 * This is also named "equality modulo bound renaming" or "equality modulo alpha-equivalence".
 * <p>
 * The single instance of this property can be accessed through
 * {@link RenamingTermProperty#RENAMING_TERM_PROPERTY}.
 *
 * @author Tobias Reinhold
 */
public class RenamingTermProperty implements Property<Term> {
    /**
     * The single instance of this property.
     */
    public static final RenamingTermProperty RENAMING_TERM_PROPERTY = new RenamingTermProperty();

    /**
     * This constructor is private as a single instance of this class should be shared. The instance
     * can be accessed through {@link RenamingTermProperty#RENAMING_TERM_PROPERTY} and is used as a
     * parameter for {@link EqualsModProperty#equalsModProperty(Object, Property, Object[])}.
     */
    private RenamingTermProperty() {}

    /**
     * Checks if {@code term2} is a term syntactically equal to {@code term1} modulo bound renaming.
     *
     * @param term1 a term
     * @param term2 the term compared to {@code term1}
     * @param v should not be used for this equality check
     * @return {@code true} iff {@code term2} has the same values in operator, sort, arity,
     *         varsBoundHere and javaBlock as {@code term1} modulo bound renaming
     * @param <V> is not needed for this equality check
     */
    @Override
    public <V> boolean equalsModThisProperty(Term term1, Term term2, V... v) {
        if (term2 == term1) {
            return true;
        }
        return unifyHelp(term1, term2, ImmutableSLList.nil(),
            ImmutableSLList.nil(), null);
    }

    /**
     * Computes the hash code of {@code term} modulo bound renaming.
     *
     * @param term the term to compute the hash code for
     * @return the hash code
     */
    @Override
    public int hashCodeModThisProperty(Term term) {
        // Labels can be completely ignored
        return hashTermHelper(term, ImmutableSLList.nil(), 1);
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

        if (t0.sort() != t1.sort() || t0.arity() != t1.arity()) {
            return false;
        }

        final Operator op0 = t0.op();

        if (op0 instanceof QuantifiableVariable) {
            return handleQuantifiableVariable(t0, t1, ownBoundVars, cmpBoundVars);
        }

        final Operator op1 = t1.op();

        if (op0 instanceof Modality mod0 && op1 instanceof Modality mod1) {
            if (mod0.kind() != mod1.kind()) {
                return false;
            }
            nat = handleJava(mod0.program(), mod1.program(), nat);
            if (nat == FAILED) {
                return false;
            }
        } else if (!(op0 instanceof ProgramVariable) && op0 != op1) {
            return false;
        }

        if (!(op0 instanceof SchemaVariable) && op0 instanceof ProgramVariable pv0) {
            if (op1 instanceof ProgramVariable pv1) {
                nat = checkNat(nat);
                if (!pv0.equalsModProperty(pv1, RENAMING_SOURCE_ELEMENT_PROPERTY, nat)) {
                    return false;
                }
            } else {
                return false;
            }
        }

        return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    /**
     * Handles the case where the first term is a quantifiable variable.
     *
     * @param t0 the first term
     * @param t1 the second term
     * @param ownBoundVars variables bound above the current position in {@code t0}
     * @param cmpBoundVars variables bound above the current position in {@code t1}
     * @return <code>true</code> iff the quantifiable variables are equal modulo renaming
     */
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

    /**
     * Checks whether the given {@link JavaBlock}s are equal modulo renaming and returns the updated
     * {@link NameAbstractionTable} or {@link #FAILED} if the {@link JavaBlock}s are not equal.
     *
     * @param jb0 the first {@link JavaBlock} to compare
     * @param jb1 the second {@link JavaBlock} to compare
     * @param nat the {@link NameAbstractionTable} used for the comparison
     * @return the updated {@link NameAbstractionTable} if the {@link JavaBlock}s are equal modulo
     *         renaming or {@link #FAILED} if they are not
     */
    private static NameAbstractionTable handleJava(JavaBlock jb0, JavaBlock jb1,
            NameAbstractionTable nat) {
        if (!jb0.isEmpty() || !jb1.isEmpty()) {
            nat = checkNat(nat);
            if (javaBlocksNotEqualModRenaming(jb0, jb1, nat)) {
                return FAILED;
            }
        }
        return nat;
    }

    /**
     * Returns true if the given {@link JavaBlock}s are not equal modulo renaming.
     * <p>
     * Moved here from {@link JavaBlock} while refactoring equalsModRenaming in {@link Term}.
     * As the implementation of equalsModRenaming in {@link JavaBlock} was only used in
     * {@link RenamingTermProperty#handleJava(JavaBlock, JavaBlock, NameAbstractionTable)}
     * and the deprecated class de.uka.ilkd.key.strategy.quantifierHeuristics.EqualityConstraint,
     * it is now only a helper method in {@link RenamingTermProperty}.
     *
     * @param jb1 the first {@link JavaBlock}
     * @param jb2 the second {@link JavaBlock}
     * @param nat the {@link NameAbstractionTable} used for the comparison
     * @return true if the given {@link JavaBlock}s are NOT equal modulo renaming
     */
    public static boolean javaBlocksNotEqualModRenaming(JavaBlock jb1, JavaBlock jb2,
            NameAbstractionTable nat) {
        JavaProgramElement pe1 = jb1.program();
        JavaProgramElement pe2 = jb2.program();
        if (pe1 == null && pe2 == null) {
            return false;
        } else if (pe1 != null && pe2 != null) {
            return !pe1.equalsModProperty(pe2, RENAMING_SOURCE_ELEMENT_PROPERTY, nat);
        }
        return true;
    }

    /**
     * Recursively descends into the subterms of the given terms and checks if they are equal modulo
     * renaming.
     *
     * @param t0 the first term
     * @param t1 the second term
     * @param ownBoundVars variables bound above the current position in {@code t0}
     * @param cmpBoundVars variables bound above the current position in {@code t1}
     * @param nat the {@link NameAbstractionTable} used for the comparison
     * @return <code>true</code> iff the subterms are equal modulo renaming
     */
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


    /**
     * Checks if the given {@link NameAbstractionTable} is not null. If it is null, a new
     * {@link NameAbstractionTable} is created and returned.
     *
     * @param nat the {@link NameAbstractionTable} to check
     * @return the given {@code nat} if it is not null, a new {@link NameAbstractionTable} otherwise
     */
    private static NameAbstractionTable checkNat(NameAbstractionTable nat) {
        if (nat == null) {
            return new NameAbstractionTable();
        }
        return nat;
    }
    // end of equals modulo renaming logic


    /* -------- Helper methods for hashCodeModThisProperty --------- */

    /**
     * Helps to compute the hash code of a term modulo bound renaming.
     * <p>
     * This method takes care of the top level of the term and calls the recursive helper method
     * {@link #recursiveHelper(Term, ImmutableList, int)} to take care of the subterms.
     *
     * @param term the term to compute the hash code for
     * @param nameAbstractionList the list of bound variables that is used to abstract from the
     *        variable names
     * @param hashCode the accumulated hash code (should be 1 for the first call)
     * @return the hash code
     */
    private int hashTermHelper(Term term, ImmutableList<QuantifiableVariable> nameAbstractionList,
            int hashCode) {
        // mirrors the implementation of unifyHelp that is responsible for equality modulo renaming
        hashCode = 17 * hashCode + term.sort().hashCode();
        hashCode = 17 * hashCode + term.arity();

        final Operator op = term.op();
        if (op instanceof QuantifiableVariable qv) {
            hashCode = 17 * hashCode + hashQuantifiableVariable(qv, nameAbstractionList);
        } else if (op instanceof Modality mod) {
            hashCode = 17 * hashCode + mod.kind().hashCode();
            hashCode = 17 * hashCode + hashJavaBlock(mod);
        } else if (op instanceof ProgramVariable pv) {
            hashCode = 17 * hashCode + pv.hashCodeModProperty(RENAMING_SOURCE_ELEMENT_PROPERTY);
        }

        return recursiveHelper(term, nameAbstractionList, hashCode);
    }

    /**
     * Computes the hash code of a quantifiable variable modulo bound renaming.
     * <p>
     * If the variable is bound, the hash code is computed based on the index of the variable in the
     * list of bound variables.
     * If the variable is not bound, the hash code is computed based on the variable itself.
     *
     * @param qv the {@link QuantifiableVariable} to compute the hash code for
     * @param nameAbstractionList the list of bound variables that is used to abstract from the
     *        variable names
     * @return the hash code
     */
    private int hashQuantifiableVariable(QuantifiableVariable qv,
            ImmutableList<QuantifiableVariable> nameAbstractionList) {
        final int index = indexOf(qv, nameAbstractionList);
        // if the variable is bound, we just need to consider the place it is bound at and abstract
        // from the name
        return index == -1 ? qv.hashCode() : index;
    }

    /**
     * Computes the hash code of a Java block modulo bound renaming.
     * <p>
     * The hash code is computed based on the hash code of the program element of the Java block.
     *
     * @param mod the {@link Modality} to compute the hash code for
     * @return the hash code
     */
    private int hashJavaBlock(Modality mod) {
        final JavaBlock jb = mod.program();
        if (!jb.isEmpty()) {
            final JavaProgramElement jpe = jb.program();
            return jpe != null ? jpe.hashCodeModProperty(RENAMING_SOURCE_ELEMENT_PROPERTY) : 0;
        }
        // if the Java block is empty, we do not add anything to the hash code
        return 0;
    }

    /**
     * Recursively computes the hash code of a term modulo bound renaming.
     * <p>
     * This method iterates over the subterms of the given term and calls
     * {@link #hashTermHelper(Term, ImmutableList, int)} for each subterm.
     *
     * @param term the term to compute the hash code for
     * @param nameAbstractionList the list of bound variables that is used to abstract from the
     *        variable names
     * @param hashCode the accumulated hash code
     * @return the hash code
     */
    private int recursiveHelper(Term term, ImmutableList<QuantifiableVariable> nameAbstractionList,
            int hashCode) {
        for (int i = 0; i < term.arity(); i++) {
            ImmutableList<QuantifiableVariable> subBoundVars = nameAbstractionList;

            for (int j = 0; j < term.varsBoundHere(i).size(); j++) {
                final QuantifiableVariable qVar = term.varsBoundHere(i).get(j);
                hashCode = 17 * hashCode + qVar.sort().hashCode();
                subBoundVars = subBoundVars.prepend(qVar);
            }

            hashCode = hashTermHelper(term.sub(i), subBoundVars, hashCode);
        }
        return hashCode;
    }

    /* ----- End of helper methods for hashCodeModThisProperty ----- */
}
