package org.key_project.isabelletranslation.automation;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.AbstractExternalSolverRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import org.key_project.logic.Name;
import org.key_project.util.collection.ImmutableList;

public class IsabelleRuleApp extends AbstractExternalSolverRuleApp {
    public static final IsabelleRule RULE = new IsabelleRule();

    protected IsabelleRuleApp(IsabelleRule rule, PosInOccurrence pio, String successfulSolverName, String successfulTactic) {
        this(rule, pio, null, successfulSolverName, "Isabelle " + successfulSolverName + ": " + successfulTactic);
    }

    protected IsabelleRuleApp(IsabelleRule rule, PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts, String successfulSolverName) {
        this(rule, pio, ifInsts, successfulSolverName, "Isabelle: " + successfulSolverName);
    }

    private IsabelleRuleApp(IsabelleRule rule, PosInOccurrence pio, ImmutableList<PosInOccurrence> ifInsts, String successfulSolverName, String title) {
        super(rule, pio, ifInsts, successfulSolverName, title);
    }



    @Override
    public AbstractExternalSolverRuleApp setTitle(String title) {
        return new IsabelleRuleApp(RULE, pio, ifInsts, successfulSolverName, title);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return new IsabelleRuleApp(RULE, newPos, successfulSolverName, title);
    }

    public static class IsabelleRule implements ExternalSolverRule {
        Name name = new Name("IsabelleRule");

        @Override
        public ExternalSolverRule newRule() {
            return new IsabelleRule();
        }

        public AbstractExternalSolverRuleApp createApp(String successfulSolverName, String successfulTactic) {
            return new IsabelleRuleApp(this, null, successfulSolverName, successfulTactic);
        }

        @Override
        public AbstractExternalSolverRuleApp createApp(String successfulSolverName) {
            return new IsabelleRuleApp(this, null, successfulSolverName, "");
        }

        @Override
        public AbstractExternalSolverRuleApp createApp(String successfulSolverName, ImmutableList<PosInOccurrence> unsatCore) {
            return new IsabelleRuleApp(this, null, unsatCore, successfulSolverName);
        }

        @Override
        public AbstractExternalSolverRuleApp createApp(PosInOccurrence pos, TermServices services) {
            return new IsabelleRuleApp(this, null, "", "");
        }

        /**
         * Create a new goal (to be closed in {@link Goal#apply(RuleApp)} directly afterwards)
         * with the same sequent as the given one.
         *
         * @param goal the Goal on which to apply <tt>ruleApp</tt>
         * @param services the Services with the necessary information about the java programs
         * @param ruleApp the rule application to be executed
         * @return a list with an identical goal as the given <tt>goal</tt>
         */
        @Override
        public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) {
            if (goal.proof().getInitConfig().getJustifInfo().getJustification(RULE) == null) {
                goal.proof().getInitConfig().registerRule(RULE, () -> false);
            }
            return goal.split(1);
        }

        @Override
        public String toString() {
            return displayName();
        }

        @Override
        public String displayName() {
            return "Isabelle";
        }

        @Override
        public Name name() {
            return name;
        }
    }
}
