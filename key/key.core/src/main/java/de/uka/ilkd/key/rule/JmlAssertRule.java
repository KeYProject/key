package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.util.MiscTools;
import org.key_project.util.collection.ImmutableList;

import java.util.Optional;

/**
 * A rule for JML assert/assume statements.
 *
 * This implements the rules as:
 *
 * <p>
 * {@code
 *    \DELTA => update(cond -> <.. ...>), \GAMMA
 * --------------------------------------------------------
 *    \DELTA => update(<.. //@assume cond; ...>), \GAMMA
 * }
 * </p>
 *
 * and
 *
 * <p>
 * {@code
 *    \DELTA => update(cond), \GAMMA   \DELTA => update(cond -> <.. ...>), \GAMMA
 * ---------------------------------------------------------------------------------
 *             \DELTA => update(<.. //@assert cond; ...>), \GAMMA
 * }
 * </p>
 *
 * @author Benjamin Takacs
 */
public final class JmlAssertRule implements BuiltInRule {

    /**
     * The instance of this rule
     */
    public static final JmlAssertRule INSTANCE = new JmlAssertRule();
    /**
     * The name of this rule
     */
    private static final Name NAME = new Name("JML assert");

    //Only one instance of this class is needed and should be there
    private JmlAssertRule() { }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence occurrence) {
        if (AbstractAuxiliaryContractRule.occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }

        Term target = occurrence.subTerm();
        if (target.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(target);
        }
        return JavaTools.getActiveStatement(target.javaBlock()) instanceof JmlAssert;
    }

    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence occurrence, TermServices services) {
        return new JmlAssertBuiltInRuleApp(this, occurrence);
    }

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp)
            throws RuleAbortException {
        if (!(ruleApp instanceof JmlAssertBuiltInRuleApp)) {
            throw new IllegalArgumentException("can only apply JmlAssertBuiltInRuleApp");
        }
        final TermBuilder tb = services.getTermBuilder();
        final PosInOccurrence occurrence = ruleApp.posInOccurrence();

        final Term formula = occurrence.subTerm();
        final Term update = UpdateApplication.getUpdate(formula);

        Term target = formula;
        if (formula.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(formula);
        }

        final JmlAssert jmlAssert = Optional
                .ofNullable(JavaTools.getActiveStatement(target.javaBlock()))
                .filter(JmlAssert.class::isInstance)
                .map(JmlAssert.class::cast)
                .orElseThrow(() -> new RuleAbortException("not a JML assert statement"));

        final MethodFrame frame = JavaTools.getInnermostMethodFrame(target.javaBlock(),
                services);
        final Term self = MiscTools.getSelfTerm(frame, services);

        final Term condition = jmlAssert.getCond(self, services);

        final ImmutableList<Goal> result;
        if (jmlAssert.getKind() == TextualJMLAssertStatement.Kind.ASSERT) {
            result = goal.split(2);
            setUpValidityRule(result.tail().head(), occurrence, update, condition, tb);
        } else if (jmlAssert.getKind() == TextualJMLAssertStatement.Kind.ASSUME) {
            result = goal.split(1);
        } else {
            throw new RuleAbortException(
                    String.format("Unknown assertion type %s", jmlAssert.getKind()));
        }
        setUpUsageGoal(result.head(), occurrence, update, target, condition, tb, services);

        return result;
    }

    private void setUpValidityRule(Goal goal, PosInOccurrence occurrence,
                                   Term update, Term condition, TermBuilder tb) {
        goal.setBranchLabel("Validity");
        goal.changeFormula(new SequentFormula(tb.apply(update, condition)), occurrence);
    }

    private void setUpUsageGoal(Goal goal, PosInOccurrence occurrence,
                                Term update, Term target, Term condition,
                                TermBuilder tb, Services services) {
        goal.setBranchLabel("Usage");
        final JavaBlock javaBlock = JavaTools.removeActiveStatement(target.javaBlock(), services);
        final Term newTerm = tb.apply(update,
                                      tb.imp(condition,
                                             tb.prog((Modality) target.op(),
                                                     javaBlock, target.sub(0), null)));

        goal.changeFormula(new SequentFormula(newTerm), occurrence);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public String displayName() {
        return NAME.toString();
    }
}
