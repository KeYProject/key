package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.ProgramPrefixUtil;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.java.visitor.ProgramElementReplacer;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.jml.translation.JMLSpecFactory;
import de.uka.ilkd.key.speclang.jml.translation.ProgramVariableCollection;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import org.key_project.util.collection.ImmutableList;

import java.util.Optional;

public class JmlAssertRule implements BuiltInRule {

    private static final Name NAME = new Name("JML assert");
    public static final JmlAssertRule INSTANCE = new JmlAssertRule();

    public static Optional<SourceElement> getFirstActiveStatement(PosInOccurrence occurrence) {
        Term formula = occurrence.subTerm();
        Term target = formula;
        //TODO: this just works for one update so you have to simplify them first
        //      should this be changed to allow any number of chained updates?
        if (formula.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(formula);
        }

        SourceElement element = target.javaBlock().program().getFirstElement();
        while ((element instanceof ProgramPrefix || element instanceof CatchAllStatement)
               && !(element instanceof StatementBlock
                    && ((StatementBlock) element).isEmpty())) {
            if (element instanceof StatementContainer) {
                element = ((StatementContainer) element).getStatementAt(0);
            } else {
                element = element.getFirstElement();
            }
        }
        return Optional.ofNullable(element);
    }

    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence occurrence) {
        //TODO: copied from blockcontractrules see if it is correct here
        if (AbstractAuxiliaryContractRule.occursNotAtTopLevelInSuccedent(occurrence)) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(occurrence)) {
            return false;
        }
        return getFirstActiveStatement(occurrence).filter(JmlAssert.class::isInstance).isPresent();
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
    public ImmutableList<Goal> apply(Goal goal, Services services, RuleApp ruleApp) throws RuleAbortException {
        assert ruleApp instanceof JmlAssertBuiltInRuleApp;
        final TermBuilder tb = services.getTermBuilder();
        final PosInOccurrence occurrence = ruleApp.posInOccurrence();
        assert occurrence != null;

        final Term formula = occurrence.subTerm();
        final Term update = UpdateApplication.getUpdate(formula);

        Term target = formula;
        if (formula.op() instanceof UpdateApplication) {
            target = UpdateApplication.getTarget(formula);
        }

        final JmlAssert jmlAssert = getFirstActiveStatement(occurrence)
                .filter(JmlAssert.class::isInstance)
                .map(JmlAssert.class::cast)
                .orElseThrow(() -> new RuleAbortException("not a JML assert statement"));

        //XXX: I think there should always be a ProgramPrefix around and stuff
        ProgramPrefixUtil.ProgramPrefixInfo info = ProgramPrefixUtil.computeEssentials((ProgramPrefix) target.javaBlock().program());
        final IProgramMethod pm = info.getInnerMostMethodFrame().getProgramMethod();
        JMLSpecFactory jsf = new JMLSpecFactory(services);

        final ProgramVariableCollection pv = jsf.createProgramVariables(pm);

        //TODO: seems like I still miss local variables here
        JmlIO jmlIo = new JmlIO(services, pm.getContainerType(), pv.selfVar, pv.paramVars,
                                pv.resultVar, pv.excVar, pv.atPres, pv.atBefores);

        //TODO: is this enought to validate that condition is side effect free?
        final Term condition = jmlIo.translateTerm(jmlAssert.getCondition(),
                jmlAssert.getKind() == TextualJMLAssertStatement.Kind.ASSERT ? OriginTermLabel.SpecType.ASSERT : OriginTermLabel.SpecType.ASSUME);

        final ImmutableList<Goal> result;
        if (jmlAssert.getKind() == TextualJMLAssertStatement.Kind.ASSERT) {
            result = goal.split(2);
            setUpUsageGoal(result.head(), occurrence, update, target, condition, jmlAssert, tb, services);
            setUpValidityRule(result.tail().head(), occurrence, update, condition, tb);
        } else if (jmlAssert.getKind() == TextualJMLAssertStatement.Kind.ASSUME) {
            result = goal.split(1);
            setUpUsageGoal(result.head(), occurrence, update, target, condition, jmlAssert, tb, services);
        } else {
            throw new RuleAbortException(String.format("Unknown assertion type %s", jmlAssert.getKind()));
        }

        return result;
    }

    private void setUpValidityRule(Goal goal, PosInOccurrence occurrence, Term update, Term condition, TermBuilder tb) {
        goal.setBranchLabel("Validity");
        goal.changeFormula(new SequentFormula(tb.apply(update, condition)), occurrence);
    }

    private void setUpUsageGoal(Goal goal, PosInOccurrence occurrence, Term update, Term target, Term condition, JmlAssert jmlAssert, TermBuilder tb, Services services) {
        goal.setBranchLabel("Usage");

        //TODO: this is there to create a new program without the first active statement
        //      there probably is a better way to do that
        final Statement prog = (Statement) new ProgramElementReplacer(target.javaBlock().program(), services).replace(jmlAssert, KeYJavaASTFactory.emptyStatement());
        final JavaBlock javaBlock = JavaBlock.createJavaBlock(prog instanceof StatementBlock ? (StatementBlock) prog : new StatementBlock(prog));
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
