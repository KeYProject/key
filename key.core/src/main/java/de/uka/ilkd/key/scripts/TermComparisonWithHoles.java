package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.logic.op.*;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static de.uka.ilkd.key.scripts.TermWithHoles.*;

/**
 * A property that can be used for comparisons for terms.
 * All term labels are ignored in this equality check. Additionally, holes (represented by the
 * SortDependingFunction with name "_" and the Predicate with name "__") are treated as wildcards that
 * match any subterm.
 *
 * @author Mattias Ulbrich
 */
@NullMarked
public class TermComparisonWithHoles {

    private final JTerm referenceTerm;

    TermComparisonWithHoles(JTerm referenceTerm) {
        this.referenceTerm = referenceTerm;
    }

    public final boolean matches(PosInOccurrence pio) {
        JTerm term = (JTerm) pio.subTerm();
        if (term.equalsModProperty(referenceTerm, RenamingTermProperty.RENAMING_TERM_PROPERTY)) {
            return true;
        }

        PosInTerm focus = findFocus(referenceTerm);
        if(focus == null) {
            focus = PosInTerm.getTopLevel();
        }

        List<PosInTerm> focusPaths = new ArrayList<>();
        expandFocusPaths(focus, pio.posInTerm(), PosInTerm.getTopLevel(), focusPaths);

        for(PosInTerm fpath : focusPaths) {
            PosInTerm pit = pio.posInTerm().firstN(pio.depth() - fpath.depth());
            JTerm startTerm = (JTerm) pit.getSubTerm(pio.sequentFormula().formula());

            boolean result = unifyHelp(referenceTerm, startTerm,
                    ImmutableSLList.<QuantifiableVariable>nil(),
                    ImmutableSLList.<QuantifiableVariable>nil(),
                    fpath);
            if (result) {
                return true;
            }
        }

        return false;
    }

    private void expandFocusPaths(PosInTerm focus, PosInTerm input, PosInTerm base, List<PosInTerm> collected) {
        if(focus.isTopLevel()) {
            // fully matched:
            collected.add(base);
            return;
        }

        if(input.isTopLevel()) {
            // input is too shallow
            return;
        }

        if(focus.getIndex() == (char)-1) {
            // ellipsis found, we need to expand
            expandFocusPaths(focus.up(), input, base, collected);
            expandFocusPaths(focus, input.up(), base.prepend((char) input.getIndex()), collected);
        } else {
            if(focus.getIndex() == input.getIndex()) {
                expandFocusPaths(focus.up(), input.up(), base.prepend((char) input.getIndex()), collected);
            } else {
                // mismatch
                return;
            }
        }
    }

    public final boolean matchesToplevel(SequentFormula sf) {
        // we use antecedent here since it does not matter and is never read ...
        return matches(new PosInOccurrence(sf, PosInTerm.getTopLevel(), true));
    }

    private static @Nullable PosInTerm findFocus(Term pattern) {
        var op = pattern.op();
        if (op instanceof JFunction) {
            if(op.name().equals(TermWithHoles.FOCUS_NAME)) {
                return PosInTerm.getTopLevel();
            }
            if(op.name().equals(TermWithHoles.ELLIPSIS_NAME)) {
                PosInTerm subFocus = findFocus(pattern.sub(0));
                if(subFocus != null) {
                    return subFocus.prepend((char)-1);
                } else {
                    return null;
                }
            }
        }
        for (int i = 0; i < pattern.arity(); i++) {
            Term sub = pattern.sub(i);
            PosInTerm subFocus = findFocus(sub);
            if(subFocus != null) {
                return subFocus.prepend((char)i);
            }
        }
        return null;
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
                                     @Nullable PosInTerm expectedFocus) {

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
        } else if(op.name().equals(FOCUS_NAME)) {
            if(expectedFocus == null || !expectedFocus.isTopLevel()) {
                // focus annotation not at expected position
                return false;
            }
            return unifyHelp(t0.sub(0), t1, ownBoundVars, cmpBoundVars, null);
        } else if(op.name().equals(ELLIPSIS_NAME)) {
            // return true if it hits one subterm ...
            Set<Pair<JTerm, PosInTerm>> deepAllSubs = new HashSet<>();
            computeSubterms(t1, expectedFocus, deepAllSubs);
            var lookfor = t0.sub(0);
            return deepAllSubs.stream().anyMatch(t -> unifyHelp(lookfor, t.first, ownBoundVars, cmpBoundVars, t.second));
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

        return descendRecursively(t0, t1, ownBoundVars, cmpBoundVars, expectedFocus);
    }

    private static void computeSubterms(JTerm t, @Nullable PosInTerm expectedPos, Set<Pair<JTerm, @Nullable PosInTerm>> deepAllSubs) {
        deepAllSubs.add(new Pair<>(t, expectedPos));
        for(int i = 0; i < t.arity(); i++) {
            computeSubterms(t.sub(i), nextFocusPos(expectedPos, i), deepAllSubs);
        }
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
                                              PosInTerm expectedFocus) {

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

            PosInTerm nextFocus = nextFocusPos(expectedFocus, i);

            boolean newConstraint = unifyHelp(t0.sub(i), t1.sub(i),
                    subOwnBoundVars, subCmpBoundVars, nextFocus);

            if (!newConstraint) {
                return false;
            }
        }

        return true;
    }

    private static @Nullable PosInTerm nextFocusPos(PosInTerm expectedFocus, int i) {
        if(expectedFocus != null && !expectedFocus.isTopLevel() && expectedFocus.getIndexAt(0) == i) {
            // we are on the path to the focus
            return expectedFocus.lastN(expectedFocus.depth() - 1);
        } else {
            return null;
        }
    }

    public List<Pair<Boolean, SequentFormula>> findTopLevelMatchesInSequent(Sequent sequent) {
        List<Pair<Boolean, SequentFormula>> matches = new ArrayList<>();
        for (SequentFormula sf : sequent.antecedent()) {
            if (matchesToplevel(sf)) {
                matches.add(new Pair<>(true, sf));
            }
        }
        for (SequentFormula sf : sequent.succedent()) {
            if (matchesToplevel(sf)) {
                matches.add(new Pair<>(false, sf));
            }
        }
        return matches;
    }


    public @Nullable Pair<Boolean, SequentFormula> findUniqueToplevelMatchInSequent(Sequent sequent) {
        List<Pair<Boolean, SequentFormula>> matches = findTopLevelMatchesInSequent(sequent);
        if (matches.size() != 1) {
            return null;
        } else {
            return matches.getFirst();
        }
    }
}
