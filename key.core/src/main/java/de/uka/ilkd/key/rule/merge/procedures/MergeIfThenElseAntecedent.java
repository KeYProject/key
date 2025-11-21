/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge.procedures;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.util.mergerule.MergeRuleUtils;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

/**
 * Rule that merges two sequents based on the if-then-else construction: If two locations are
 * assigned different values in the states, the value in the merged state is chosen based on the
 * path condition. This rule retains total precision. In contrast to the {@link MergeByIfThenElse}
 * rule, the distinction is not realized in the update / symbolic state, but in the antecedent /
 * path condition. This can be much more efficient.
 *
 * @author Dominic Scheurer
 * @see MergeByIfThenElse
 * @see MergeRule
 */
public class MergeIfThenElseAntecedent extends MergeProcedure
        implements UnparametricMergeProcedure {

    private static MergeIfThenElseAntecedent INSTANCE = null;

    public static MergeIfThenElseAntecedent instance() {
        if (INSTANCE == null) {
            INSTANCE = new MergeIfThenElseAntecedent();
        }
        return INSTANCE;
    }

    private static final String DISPLAY_NAME = "MergeByIfThenElseAntecedent";

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.rule.merge.MergeProcedure#complete()
     */
    @Override
    public boolean complete() {
        return true;
    }

    @Override
    public ValuesMergeResult mergeValuesInStates(JTerm v, SymbolicExecutionState state1,
            JTerm valueInState1, SymbolicExecutionState state2, JTerm valueInState2,
            JTerm distinguishingFormula, Services services) {

        final TermBuilder tb = services.getTermBuilder();

        Function newSkolemConst = MergeRuleUtils
                .getNewSkolemConstantForPrefix(v.op().name().toString(), v.sort(), services);
        LinkedHashSet<Name> newNames = new LinkedHashSet<>();
        newNames.add(newSkolemConst.name());

        ImmutableSet<JTerm> newConstraints = DefaultImmutableSet.nil();
        newConstraints = newConstraints.union(getIfThenElseConstraints(tb.func(newSkolemConst),
            valueInState1, valueInState2, state1, state2, distinguishingFormula, services));

        return new ValuesMergeResult(newConstraints, tb.func(newSkolemConst), newNames,
            new LinkedHashSet<>());

    }

    @Override
    public boolean requiresDistinguishablePathConditions() {
        return true;
    }

    /**
     * Returns a list of if-then-else constraints for the given constrained term, states and if/else
     * terms.
     *
     * @param constrained The constrained term.
     * @param ifTerm The value for the if case.
     * @param elseTerm The value for the else case.
     * @param state1 First SE state ("if").
     * @param state2 Second SE state ("else").
     * @param distinguishingFormula The user-specified distinguishing formula. May be null (for
     *        automatic generation).
     * @param services The services object.
     * @return A list of if-then-else constraints for the given constrained term, states and if/else
     *         terms.
     */
    private static ImmutableSet<JTerm> getIfThenElseConstraints(JTerm constrained, JTerm ifTerm,
            JTerm elseTerm, SymbolicExecutionState state1, SymbolicExecutionState state2,
            JTerm distinguishingFormula, Services services) {

        final TermBuilder tb = services.getTermBuilder();
        ImmutableSet<JTerm> result = DefaultImmutableSet.nil();

        if (distinguishingFormula == null) {
            final MergeByIfThenElse.DistanceFormRightSide distFormAndRightSidesForITEUpd =
                MergeByIfThenElse.createDistFormAndRightSidesForITEUpd(state1, state2, ifTerm,
                    elseTerm, services);

            final JTerm cond = distFormAndRightSidesForITEUpd.distinguishingFormula();
            final JTerm ifForm = distFormAndRightSidesForITEUpd.ifTerm();
            final JTerm elseForm = distFormAndRightSidesForITEUpd.elseTerm();
            final boolean isSwapped = distFormAndRightSidesForITEUpd.sideCommuted();

            final JTerm varEqualsIfForm = tb.equals(constrained, ifForm);
            final JTerm varEqualsElseForm = tb.equals(constrained, elseForm);

            if (!(ifTerm.equals(constrained) && !isSwapped
                    || elseTerm.equals(constrained) && isSwapped)) {
                result = result.add(tb.imp(cond, varEqualsIfForm));
            }

            if (!(elseTerm.equals(constrained) && !isSwapped
                    || ifTerm.equals(constrained) && isSwapped)) {
                result = result.add(tb.or(cond, varEqualsElseForm));
            }
        } else {
            final JTerm varEqualsIfForm = tb.equals(constrained, ifTerm);
            final JTerm varEqualsElseForm = tb.equals(constrained, elseTerm);

            result = result.add(tb.imp(distinguishingFormula, varEqualsIfForm));
            result = result.add(tb.or(distinguishingFormula, varEqualsElseForm));
        }

        return result;

    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }
}
