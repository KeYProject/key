package de.uka.ilkd.key.smt;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
/**
 * The rule application that is used when a goal is closed by means of an external solver. So far it
 * stores the rule that that has been used and a title containing some information for the user.
 */
public class RuleAppSMT extends AbstractBuiltInRuleApp {

    public final static SMTRule RULE = new SMTRule();
    private final String title;
    private final String successfulSolverName;


    RuleAppSMT(SMTRule rule, String successfulSolverName) {
        super(rule, null, null);
        this.title = "SMT: " + successfulSolverName;
        this.successfulSolverName = successfulSolverName;
    }

    RuleAppSMT(SMTRule rule, String successfulSolverName, ImmutableList<PosInOccurrence> unsatCore) {
        super(rule, null, unsatCore);
        this.title = "SMT: " + successfulSolverName;
        this.successfulSolverName = successfulSolverName;
    }

    @Deprecated
    private RuleAppSMT(SMTRule rule, ImmutableList<PosInOccurrence> ifInsts,
            String title, String successfulSolverName) {
        super(rule, null, ifInsts);
        this.title = title;
        this.successfulSolverName = successfulSolverName;
    }


    private RuleAppSMT(String title, String successfulSolverName) {
        super(RULE, null);
        this.title = title;
        this.successfulSolverName = successfulSolverName;
    }

    public RuleAppSMT replacePos(PosInOccurrence newPos) {
        return this;
    }

    @Override
    public boolean complete() {
        return true;
    }

    public String getTitle() {
        return title;
    }

    public String getSuccessfulSolverName() {
        return successfulSolverName;
    }

    @Override
    public PosInOccurrence posInOccurrence() {
        return null;
    }

    @Override
    public BuiltInRule rule() {

        return RULE;
    }

    public static class SMTRule implements BuiltInRule {
        public static final Name name = new Name("SMTRule");

        public RuleAppSMT createApp(String successfulSolverName) {
            return new RuleAppSMT(this, successfulSolverName);
        }

        /**
         * Create a new rule application with the given solver name and unsat core.
         *
         * @param successfulSolverName solver that produced this result
         * @param unsatCore formulas required to prove the result
         * @return rule application instance
         */
        public RuleAppSMT createApp(String successfulSolverName, ImmutableList<PosInOccurrence> unsatCore) {
            return new RuleAppSMT(this, successfulSolverName, unsatCore);
        }

        @Override
        public RuleAppSMT createApp(PosInOccurrence pos, TermServices services) {
            return new RuleAppSMT(this, "");
        }


        @Override
        public boolean isApplicable(Goal goal, PosInOccurrence pio) {
            return false;
        }


        @Override
        public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
            if (goal.proof().getInitConfig().getJustifInfo().getJustification(RULE) == null) {
                goal.proof().getInitConfig().registerRule(RULE, () -> false);
            }

            // RuleAppSMT app = (RuleAppSMT) ruleApp;
            // goal.node().getNodeInfo().setBranchLabel(app.getTitle());
            ImmutableList<Goal> newGoals = goal.split(0);

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

    @Deprecated
    public RuleAppSMT setTitle(String title) {
        return new RuleAppSMT(title, successfulSolverName);
    }

    @Override
    public RuleAppSMT setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public RuleAppSMT tryToInstantiate(Goal goal) {
        return this;
    }

}
