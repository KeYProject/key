package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;

import org.key_project.util.collection.ImmutableList;

import java.util.ArrayList;
import java.util.List;

/**
 * The rule application that is used when a goal is closed by means of an external solver. So far it
 * stores the rule that that has been used and a title containing some information for the user.
 */
public class RuleAppSMT extends AbstractBuiltInRuleApp {

    public final static SMTRule rule = new SMTRule();
    private final String title;

    /**
     * Create a new rule app without ifInsts (will be null).
     * @param rule the SMTRule to apply
     * @param pio the pos in term to apply the rule on
     */
    RuleAppSMT(SMTRule rule, PosInOccurrence pio) {
        this(rule, pio, null, "SMT Rule App");
    }

    private RuleAppSMT(SMTRule rule, PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts,
                       String title) {
        super(rule, pio, ifInsts);
        this.title = title;
    }

    private RuleAppSMT(SMTRule rule, String title) {
        super(rule, null);
        this.title = title;
    }

    public RuleAppSMT replacePos(PosInOccurrence newPos) {
        return new RuleAppSMT(rule, newPos, ifInsts, title);
    }

    @Override
    public boolean complete() {
        return true;
    }

    public String getTitle() {
        return title;
    }

    @Override
    public PosInOccurrence posInOccurrence() {
        return pio;
    }

    @Override
    public BuiltInRule rule() {
        return rule;
    }

    public static class SMTRule implements BuiltInRule {
        public static final Name name = new Name("SMTRule");

        public RuleAppSMT createApp(PosInOccurrence pos) {
            return createApp(pos, null);
        }

        @Override
        public RuleAppSMT createApp(PosInOccurrence pos, TermServices services) {
            return new RuleAppSMT(this, pos);
        }


        @Override
        public boolean isApplicable(Goal goal, PosInOccurrence pio) {
            return false;
        }


        /**
         * Create a new goal (to be closed in {@link Goal#apply(RuleApp)} directly afterwards)
         * with the same sequent as the given one.
         * @param goal the Goal on which to apply <tt>ruleApp</tt>
         * @param services the Services with the necessary information about the java programs
         * @param ruleApp the rule application to be executed
         * @return a list with an identical goal as the given <tt>goal</tt>
         */
        @Override
        public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
            if (goal.proof().getInitConfig().getJustifInfo().getJustification(rule) == null) {
                goal.proof().getInitConfig().registerRule(rule, () -> false);
            }

            // RuleAppSMT app = (RuleAppSMT) ruleApp;
            // goal.node().getNodeInfo().setBranchLabel(app.getTitle());
            ImmutableList<Goal> newGoals = goal.split(1);

            return newGoals;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public boolean isApplicableOnSubTerms() {
            return false;
        }

        @Override
        public String displayName() {
            return "SMT";
        }

        public String toString() {
            return displayName();
        }

        @Override
        public Name name() {
            return name;
        }

    }

    public RuleAppSMT setTitle(String title) {
        return new RuleAppSMT(rule, pio, ifInsts, title);
    }

    @Override
    public RuleAppSMT setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    /**
     * Create a new RuleApp with the same pio (in this case, that will probably be null as the
     * SMT rule is applied to the complete sequent) as this one.
     * Add all top level formulas of the goal
     * to the RuleApp's ifInsts.
     * @param goal the goal to instantiate the current RuleApp on
     * @return a new RuleApp with the same pio and all top level formulas of the goal as ifInsts
     */
    @Override
    public RuleAppSMT tryToInstantiate(Goal goal) {
        RuleAppSMT app = rule.createApp(pio);
        Sequent seq = goal.sequent();
        List<PosInOccurrence> ifInsts = new ArrayList<>();
        for (SequentFormula ante : seq.antecedent()) {
            ifInsts.add(new PosInOccurrence(ante, PosInTerm.getTopLevel(), true));
        }
        for (SequentFormula succ : seq.succedent()) {
            ifInsts.add(new PosInOccurrence(succ, PosInTerm.getTopLevel(), false));
        }
        return app.setIfInsts(ImmutableList.fromList(ifInsts));
    }

}
