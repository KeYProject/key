package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.MiscTools;

/**
 * The built in rule app for the loop invariant rule.
 */
public class LoopInvariantBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private final While loop;

    private final LoopInvariant inv;

    public LoopInvariantBuiltInRuleApp(BuiltInRule rule, PosInOccurrence pos) {
        this(rule, pos, null, null);
    }

    protected LoopInvariantBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts,
            LoopInvariant inv) {
        super(rule, pio, ifInsts);
        assert pio != null;
        this.inv = inv;
        this.loop = (While) MiscTools.getActiveStatement(programTerm()
                .javaBlock());
        assert loop != null;
    }

    protected LoopInvariantBuiltInRuleApp(BuiltInRule rule,
            PosInOccurrence pio, LoopInvariant inv) {
        this(rule, pio, null, inv);

    }

    public boolean complete() {
        return inv != null && loop != null && invariantAvailable()
                && (!variantRequired() || variantAvailable());
    }

    public LoopInvariant getInvariant() {
        return inv;
    }

    public While getLoopStatement() {
        return loop;
    }

    public boolean invariantAvailable() {
        return inv != null && inv.getInternalInvariant() != null;
    }

    public boolean isSufficientlyComplete() {
        return pio != null && loop != null;
    }

    public Term programTerm() {
        if (posInOccurrence() != null) {
            return MiscTools.goBelowUpdates(posInOccurrence().subTerm());
        }
        return null;
    }

    @Override
    public LoopInvariantBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new LoopInvariantBuiltInRuleApp(builtInRule, newPos, ifInsts,
                inv);
    }

    public LoopInvariant retrieveLoopInvariantFromSpecification(
            Services services) {
        return services.getSpecificationRepository().getLoopInvariant(loop);
    }

    @Override
    public LoopInvariantBuiltInRuleApp setIfInsts(
            ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
        // return new InvariantBuiltInRuleApp(builtInRule, newPos, ifInsts,
        // loop, inv);

    }

    public LoopInvariantBuiltInRuleApp setLoopInvariant(LoopInvariant inv) {
        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv);
    }

    @Override
    public LoopInvariantBuiltInRuleApp tryToInstantiate(Goal goal) {
        if (inv != null) {
            return this;
        }
        final Services services = goal.proof().getServices();
        final LoopInvariant inv = retrieveLoopInvariantFromSpecification(services);

        if (inv == null) {
            return this;
        }

        return new LoopInvariantBuiltInRuleApp(builtInRule, pio, ifInsts, inv);
    }

    public boolean variantAvailable() {
        return inv != null && inv.getInternalVariant() != null;
    }

    public boolean variantRequired() {
        return ((Modality) programTerm().op()).terminationSensitive();
    }

}
