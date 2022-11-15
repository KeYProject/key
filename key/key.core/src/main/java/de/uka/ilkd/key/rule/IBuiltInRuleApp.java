package de.uka.ilkd.key.rule;

import java.util.List;
import java.util.Objects;
import java.util.stream.Stream;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;

public interface IBuiltInRuleApp extends RuleApp {

    /**
     * returns the built in rule of this rule application
     */
    BuiltInRule rule();

    /**
     * Tries to complete the rule application from the available information. Attention: Do neither
     * add GUI code to the rules nor use this method directly Instead ask the implementation of the
     * {@link de.uka.ilkd.key.control.UserInterfaceControl} to complete a built-in rule. Returns a
     * complete app only if there is exactly one contract. If you want a complete app for combined
     * contracts, use <code>forceInstantiate</code> instead. For an example implementation see e.g.
     * {@link UseOperationContractRule} or {@link UseDependencyContractRule}.
     */
    IBuiltInRuleApp tryToInstantiate(Goal goal);

    IBuiltInRuleApp forceInstantiate(Goal goal);

    List<LocationVariable> getHeapContext();

    /**
     * returns true if tryToInstantiate may be able to complete the app
     *
     * @return
     */
    boolean isSufficientlyComplete();

    ImmutableList<PosInOccurrence> ifInsts();

    IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts);

    IBuiltInRuleApp replacePos(PosInOccurrence newPos);

    @Override
    default boolean equalsModProofIrrelevancy(Object obj) {
        if (!(obj instanceof IBuiltInRuleApp)) {
            return false;
        }
        var that = (IBuiltInRuleApp) obj;
        if (!(Objects.equals(rule(), that.rule()) && Objects.equals(getHeapContext(), that.getHeapContext()))) {
            return false;
        }
        var ifInsts1 = ifInsts();
        var ifInsts2 = that.ifInsts();
        if (ifInsts1.size() != ifInsts2.size()) {
            return false;
        }
        while (!ifInsts1.isEmpty()) {
            if (!ifInsts1.head().eqEquals(ifInsts2.head())) {
                return false;
            }
            ifInsts1 = ifInsts1.tail();
            ifInsts2 = ifInsts2.tail();
        }
        return true; // TODO: check pos
    }

    @Override
    default int hashCodeModProofIrrelevancy() {
        return 0; // TODO
    }
}
