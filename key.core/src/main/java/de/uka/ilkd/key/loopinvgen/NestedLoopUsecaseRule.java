package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Transformer;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.speclang.LoopSpecification;
import org.key_project.util.collection.Pair;
import org.key_project.util.collection.ImmutableList;

public class NestedLoopUsecaseRule implements BuiltInRule {

    public final static BuiltInRule NESTED_LOOP_USECASE_RUlE = new NestedLoopUsecaseRule();
    public final static Name NESTED_LOOP_USECASE_RUlE_NAME = new Name("Nested Loop Usecase Rule");

    @Override
    public ImmutableList<Goal> apply(Goal goal, Services services,
                                     RuleApp ruleApp) throws RuleAbortException {
        final ImmutableList<Goal> newGoals = goal.split(1);
        final Goal newGoal = newGoals.head();

        final Term formula = (ruleApp.posInOccurrence().sequentFormula().formula());
        LoopStatement innerLoop = extractInnerLoop(formula);
        LoopSpecification lis = services.getSpecificationRepository().getLoopSpec(innerLoop);

        NestedLoopUsecaseRuleImp worker = new NestedLoopUsecaseRuleImp(newGoal);
        worker.nestedLoopUsecase(newGoal, ruleApp.posInOccurrence(), lis, expr2term(services, innerLoop.getGuardExpression()));

        return newGoals;
    }

    protected Term expr2term(Services services, Expression expr) {
        return services.getTypeConverter().convertToLogicElement(expr);
    }
    protected Term skipUpdates(Term formula) {
        return formula.op() instanceof UpdateApplication ? UpdateApplication.getTarget(formula) : formula;
    }
    private LoopStatement extractInnerLoop(Term f) {
        LoopStatement innerLoop =null;
        if (f.op() instanceof Modality mod && mod.kind() == JavaModalityKind.DIA) {
            ProgramElement pe = f.javaBlock().program();
            Statement activePE;
            if (pe instanceof ProgramPrefix) {
                activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
            } else {
                activePE = (Statement) pe.getFirstElement();
            }
            if (activePE instanceof While) {
                innerLoop = (LoopStatement) activePE;
            }
        }
        return innerLoop;
    }

    private LoopStatement extractOuterLoop(Term f) {
        LoopStatement outerLoop =null;
        if (f.op() instanceof Modality mod && mod.kind() == JavaModalityKind.DIA) {
            ProgramElement pe = f.javaBlock().program();
            Statement activePE;
            if (pe instanceof ProgramPrefix) {
                activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
            } else {
                activePE = (Statement) pe.getFirstElement();
            }
            if (activePE instanceof While) {
                outerLoop = (LoopStatement)((ProgramPrefix) pe).getLastPrefixElement().getNextPrefixElement();
            }
        }
        System.out.println("Outer Loop: " + outerLoop);
        return outerLoop;
    }

    @Override
    public Name name() {
        return NESTED_LOOP_USECASE_RUlE_NAME;
    }

    @Override
    public String displayName() {
        return NESTED_LOOP_USECASE_RUlE_NAME.toString();
    }


    @Override
    public boolean isApplicable(Goal goal, PosInOccurrence pio) {
        if (pio == null || !pio.isTopLevel() || pio.isInAntec()) {
            return false;
        }
        // abort if inside of transformer
        if (Transformer.inTransformer(pio)) {
            return false;
        }
        Pair<Term, Term> up = applyUpdates(pio.subTerm(), goal.proof().getServices());
        final Term progPost = up.second;
        if (!checkFocus(progPost)) {
            return false;
        }
        // active statement must be while loop
        final SourceElement activeStatement = JavaTools.getActiveStatement(progPost.javaBlock());
        if (!(activeStatement instanceof While)) {
            return false;
        }
        return true;

    }

    static Pair<Term, Term> applyUpdates(Term focusTerm, TermServices services) {
        if (focusTerm.op() instanceof UpdateApplication) {
            return new Pair<Term, Term>(UpdateApplication.getUpdate(focusTerm),
                    UpdateApplication.getTarget(focusTerm));
        } else {
            return new Pair<Term, Term>(services.getTermBuilder().skip(), focusTerm);
        }
    }


    private static boolean checkFocus(final Term progPost) {
        // focus (below update) must be modality term
        return progPost.op() instanceof Modality;
    }
    @Override
    public boolean isApplicableOnSubTerms() {
        return false;
    }

    @Override
    public IBuiltInRuleApp createApp(PosInOccurrence pos,
                                     TermServices services) {
        return new DefaultBuiltInRuleApp(this, pos);
    }

}
