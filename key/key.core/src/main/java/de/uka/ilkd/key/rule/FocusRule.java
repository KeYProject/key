package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import org.key_project.util.collection.ImmutableList;

public class FocusRule implements BuiltInRule {
    public static final FocusRule INSTANCE = new FocusRule();
    private static final Name NAME = new Name("Focus on Formula");

    class FocusRuleApp extends AbstractBuiltInRuleApp {
        protected FocusRuleApp(BuiltInRule rule, PosInOccurrence pio) {
            super(rule, pio);
        }

        @Override
        public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
            return new FocusRuleApp(rule(), newPos);
        }

        @Override
        public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
            return this;
        }

        @Override
        public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
            // TODO: ?
            return this;
        }
    }

    private FocusRule() {
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        // TODO: allow for manual application only (since this is a weakening rule and always applicable)
        // focus must be top level
        return pio != null && pio.isTopLevel();
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos, TermServices services) {
        return new FocusRuleApp(this, pos);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
        PosInOccurrence pio = ruleApp.posInOccurrence();
        SequentFormula focus = pio.sequentFormula();

        // change goal
        final ImmutableList<Goal> result = goal.split(1);
        final Goal resultGoal = result.head();
        Sequent sequent = resultGoal.sequent();

        // irreversible: we do not create insert_hidden_... taclets for the deleted formulas!
        for (SequentFormula sf : sequent.antecedent()) {
            if (!sf.equals(focus)) {
                // delete
                resultGoal.removeFormula(new PosInOccurrence(sf, PosInTerm.getTopLevel(), true));
            }
        }

        for (SequentFormula sf : sequent.succedent()) {
            if (!sf.equals(focus)) {
                // delete
                resultGoal.removeFormula(new PosInOccurrence(sf, PosInTerm.getTopLevel(), false));
            }
        }
        return result;
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }

    @Override
    public String toString() {
        return displayName();
    }
}
