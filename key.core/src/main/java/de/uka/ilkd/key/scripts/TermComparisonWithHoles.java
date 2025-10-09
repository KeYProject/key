package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.*;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.Name;
import org.key_project.logic.Property;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

import java.util.ArrayList;
import java.util.List;

import static de.uka.ilkd.key.scripts.TermWithHoles.*;

/**
 * A property that can be used for comparisons for terms.
 * All term labels are ignored in this equality check. Additionally, holes (represented by the
 * SortDependingFunction with name "_" and the Predicate with name "__") are treated as wildcards that
 * match any subterm.
 * <p>
 * The single instance of this property can be accessed through
 * {@link TermComparisonWithHoles#INSTANCE}.
 *
 * @author Mattias Ulbrich
 */
public class TermComparisonWithHoles {

    private static final NameAbstractionTable FAILED = new NameAbstractionTable();
    private final JTerm referenceTerm;

    TermComparisonWithHoles(JTerm referenceTerm) {
        this.referenceTerm = referenceTerm;
    }

    TermComparisonWithHoles(TermWithHoles twh) {
        this.referenceTerm = twh.term();
    }

    public static boolean compare(JTerm referenceTerm, JTerm concreteTerm) {
        TermComparisonWithHoles comparator = new TermComparisonWithHoles(referenceTerm);
        return comparator.compareTo(concreteTerm);
    }

    public final boolean compareTo(JTerm t) {
        if (referenceTerm == t) {
            return true;
        }
        return unifyHelp(referenceTerm, t,
                ImmutableSLList.<QuantifiableVariable>nil(),
                ImmutableSLList.<QuantifiableVariable>nil(),
                null);
    }

    public static boolean compareModHoles(JTerm t1, JTerm t2) {
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
     * @param t0           the first term -- potentially containing holes
     * @param t1           the second term
     * @param ownBoundVars variables bound above the current position
     * @param cmpBoundVars variables bound above the current position
     * @return <code>true</code> is returned iff the terms are equal modulo
     * bound renaming
     */
    private static boolean unifyHelp(JTerm t0, JTerm t1,
                                     ImmutableList<QuantifiableVariable> ownBoundVars,
                                     ImmutableList<QuantifiableVariable> cmpBoundVars,
                                     NameAbstractionTable nat) {

        if (t0 == t1 && ownBoundVars.equals(cmpBoundVars)) {
            return true;
        }

        Operator op = t0.op();
        if(op instanceof SortDependingFunction sdop) {
            if(sdop.getKind().equals(HOLE_SORT_DEP_NAME)) {
                return true;
            }
        } else if(op.name().equals(HOLE_PREDICATE_NAME) || op.name().equals(HOLE_NAME)) {
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

//        nat = handleJava(t0, t1, nat);
//        if (nat == FAILED) {
//            return false;
//        }

        return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, nat);
    }

    private static boolean handleQuantifiableVariable(JTerm t0, JTerm t1,
                                                      ImmutableList<QuantifiableVariable> ownBoundVars,
                                                      ImmutableList<QuantifiableVariable> cmpBoundVars) {
        if (!((t1.op() instanceof QuantifiableVariable) && compareBoundVariables(
                (QuantifiableVariable) t0.op(), (QuantifiableVariable) t1.op(),
                ownBoundVars, cmpBoundVars))) {
            return false;
        }
        return true;
    }

//    private static NameAbstractionTable handleJava(JTerm t0, JTerm t1,
//                                                   NameAbstractionTable nat) {
//
//        if (!t0.javaBlock().isEmpty() || !t1.javaBlock().isEmpty()) {
//            nat = checkNat(nat);
//            if (!t0.javaBlock().equalsModRenaming(t1.javaBlock(), nat)) {
//                return FAILED;
//            }
//        }
//
//        if (!(t0.op() instanceof SchemaVariable)
//                && t0.op() instanceof ProgramVariable) {
//            if (!(t1.op() instanceof ProgramVariable)) {
//                return FAILED;
//            }
//            nat = checkNat(nat);
//            if (!((ProgramVariable) t0.op()).equalsModRenaming(
//                    (ProgramVariable) t1.op(), nat)) {
//                return FAILED;
//            }
//        }
//
//        return nat;
//    }

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

    private static boolean descendRecursively(JTerm t0, JTerm t1,
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

    public List<Pair<Boolean, SequentFormula>> findMatchesInSequent(Sequent sequent) {
        List<Pair<Boolean, SequentFormula>> matches = new ArrayList<>();
        for (SequentFormula sf : sequent.antecedent()) {
            if (compareTo((JTerm) sf.formula())) {
                matches.add(new Pair<>(true, sf));
            }
        }
        for (SequentFormula sf : sequent.succedent()) {
            if (compareTo((JTerm) sf.formula())) {
                matches.add(new Pair<>(false, sf));
            }
        }
        return matches;
    }


    public @Nullable Pair<Boolean, SequentFormula> findUniqueMatchInSequent(Sequent sequent) {
        List<Pair<Boolean, SequentFormula>> matches = findMatchesInSequent(sequent);
        if (matches.size() != 1) {
            return null;
        } else {
            return matches.getFirst();
        }
    }
}
