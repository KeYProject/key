package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/** This is more a temporary hack for scripts ... */
public class TermComparisonWithHoles {

    private static final Name HOLE_NAME = new Name("_");
    private static final Name HOLE_PREDICATE_NAME = new Name("__");

    private static final NameAbstractionTable FAILED = new NameAbstractionTable();

    public static boolean compareModHoles(Term t1, Term t2) {
        if (t1 == t2) {
            return true;
        }
        return unifyHelp(t1, t2,
                ImmutableSLList.<QuantifiableVariable>nil(),
                ImmutableSLList.<QuantifiableVariable>nil(),
                null);
    }


    /**
     * Compares two terms modulo bound renaming
     *
     * @param t0           the first term
     * @param t1           the second term
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     * @return <code>true</code> is returned iff the terms are equal modulo
     * bound renaming
     */
    private static boolean unifyHelp(Term t0, Term t1,
                                     ImmutableList<QuantifiableVariable> ownBoundVars,
                                     ImmutableList<QuantifiableVariable> cmpBoundVars,
                                     NameAbstractionTable nat) {

        if (t0 == t1 && ownBoundVars.equals(cmpBoundVars)) {
            return true;
        }

        Operator op = t0.op();
        if(op instanceof SortDependingFunction) {
            var sdop = (SortDependingFunction) op;
            if(sdop.getKind().equals(HOLE_NAME)) {
                return true;
            }
        } else if(op.name().equals(HOLE_PREDICATE_NAME)) {
            return true;
        }


        final Operator op0 = t0.op();

        if (op0 instanceof QuantifiableVariable) {
            return handleQuantifiableVariable(t0, t1, ownBoundVars,
                    cmpBoundVars);
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

    private static boolean handleQuantifiableVariable(Term t0, Term t1,
                                                      ImmutableList<QuantifiableVariable> ownBoundVars,
                                                      ImmutableList<QuantifiableVariable> cmpBoundVars) {
        if (!((t1.op() instanceof QuantifiableVariable) && compareBoundVariables(
                (QuantifiableVariable) t0.op(), (QuantifiableVariable) t1.op(),
                ownBoundVars, cmpBoundVars))) {
            return false;
        }
        return true;
    }

    private static NameAbstractionTable handleJava(Term t0, Term t1,
                                                   NameAbstractionTable nat) {

        if (!t0.javaBlock().isEmpty() || !t1.javaBlock().isEmpty()) {
            nat = checkNat(nat);
            if (!t0.javaBlock().equalsModRenaming(t1.javaBlock(), nat)) {
                return FAILED;
            }
        }

        if (!(t0.op() instanceof SchemaVariable)
                && t0.op() instanceof ProgramVariable) {
            if (!(t1.op() instanceof ProgramVariable)) {
                return FAILED;
            }
            nat = checkNat(nat);
            if (!((ProgramVariable) t0.op()).equalsModRenaming(
                    (ProgramVariable) t1.op(), nat)) {
                return FAILED;
            }
        }

        return nat;
    }

    /**
     * compare two quantifiable variables if they are equal modulo renaming
     *
     * @param ownVar       first QuantifiableVariable to be compared
     * @param cmpVar       second QuantifiableVariable to be compared
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     */
    private static boolean compareBoundVariables(QuantifiableVariable ownVar,
                                                 QuantifiableVariable cmpVar,
                                                 ImmutableList<QuantifiableVariable> ownBoundVars,
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

    private static int indexOf(QuantifiableVariable var,
                               ImmutableList<QuantifiableVariable> list) {
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


    private static NameAbstractionTable checkNat(NameAbstractionTable nat) {
        if (nat == null) {
            return new NameAbstractionTable();
        }
        return nat;
    }

    private static boolean descendRecursively(Term t0, Term t1,
                                              ImmutableList<QuantifiableVariable> ownBoundVars,
                                              ImmutableList<QuantifiableVariable> cmpBoundVars,
                                              NameAbstractionTable nat) {

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

            boolean newConstraint = unifyHelp(t0.sub(i), t1.sub(i),
                    subOwnBoundVars, subCmpBoundVars, nat);

            if (!newConstraint) {
                return false;
            }
        }

        return true;
    }
}
