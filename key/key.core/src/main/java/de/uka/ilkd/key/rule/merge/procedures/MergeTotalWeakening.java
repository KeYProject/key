package de.uka.ilkd.key.rule.merge.procedures;

import static de.uka.ilkd.key.util.mergerule.MergeRuleUtils.getNewSkolemConstantForPrefix;

import java.util.LinkedHashSet;

import org.key_project.util.collection.DefaultImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.rule.merge.MergeProcedure;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

/**
 * Rule that merges two sequents based on "total" weakening: Replacement of symbolic state by an
 * update setting every program variable to a fresh Skolem constant, if the respective program
 * variable does not evaluate to the same value in both states - in this case, the original value is
 * preserved (-> idempotency).
 *
 * @author Dominic Scheurer
 */
public class MergeTotalWeakening extends MergeProcedure implements UnparametricMergeProcedure {

    private static MergeTotalWeakening INSTANCE = null;

    public static MergeTotalWeakening instance() {
        if (INSTANCE == null) {
            INSTANCE = new MergeTotalWeakening();
        }
        return INSTANCE;
    }

    private static final String DISPLAY_NAME = "MergeByFullAnonymization";

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
    public ValuesMergeResult mergeValuesInStates(Term v, SymbolicExecutionState state1,
            Term valueInState1, SymbolicExecutionState state2, Term valueInState2,
            Term distinguishingFormula, Services services) {

        final TermBuilder tb = services.getTermBuilder();

        final Function newSkolemConstant =
            getNewSkolemConstantForPrefix(v.op().name().toString(), v.sort(), services);
        LinkedHashSet<Name> newNames = new LinkedHashSet<Name>();
        newNames.add(newSkolemConstant.name());

        return new ValuesMergeResult(DefaultImmutableSet.<Term>nil(), tb.func(newSkolemConstant),
            newNames, new LinkedHashSet<Term>());

    }

    @Override
    public boolean requiresDistinguishablePathConditions() {
        return false;
    }

    @Override
    public String toString() {
        return DISPLAY_NAME;
    }
}
