package de.uka.ilkd.hoare.rule;

import java.util.LinkedList;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IteratorOfGoal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

/**
 * 
 * realises the loop invariant rule for the Hoare logic with updates
 *
 */
public class HoareLoopInvariantRule implements BuiltInRule {

    private final static Name LOOP_INV_RULENAME = new Name("Loop Invariant");
    public static final HoareLoopInvariantRule INSTANCE = new HoareLoopInvariantRule();
    private static final Name EXECTIME = new Name("executionTime");
    
    private HoareLoopInvariantRule() {
        
    }
    
    public boolean isApplicable(Goal goal, PosInOccurrence pio,
            Constraint userConstraint) {
        
        if (pio == null || pio.isInAntec() || !pio.isTopLevel() || 
                !goal.ruleAppIndex().tacletIndex().getPartialInstantiatedApps().isEmpty()) {
            return false;
        }
                        
        final ConstrainedFormula cf = pio.constrainedFormula();
        Term progFormula = cf.formula();
        
        while (progFormula.op() instanceof QuanUpdateOperator) {
            progFormula = ((QuanUpdateOperator)progFormula.op()).target(progFormula);
        }
        
        if (!(progFormula.op() instanceof Modality)) {
            return false;
        }
        
        final ProgramElement prg = progFormula.javaBlock().program();
        
        if (prg == null) {
            return false;
        }
        
        assert prg instanceof StatementBlock;
        
        final PosInProgram firstActiveChildPos = ((StatementBlock)prg).getFirstActiveChildPos();
        
        if (firstActiveChildPos == null) {
            return false;
        }
        
        return firstActiveChildPos.getProgram(prg) instanceof While;        
    }

    public ListOfGoal apply(Goal goal, Services services, RuleApp ruleApp) {
        assert ruleApp instanceof HoareLoopInvRuleApp;
        
        final HoareLoopInvRuleApp app = (HoareLoopInvRuleApp)ruleApp;
        
        final ListOfGoal goals = goal.split(3);
        
        final IteratorOfGoal it = goals.iterator();
        
        final Modality modus = modus(ruleApp.posInOccurrence());
        
        createUseCaseBranch(modus, app, it.next());

        createPreservesBranch(modus, app, it.next());
               
        createInitialBranch(modus, app, it.next());
        
        return goals;
    }

    private Term getCondition(RuleApp app, Services services) {

        final While whileS = getWhileStatement(app);        

        return services.getTypeConverter().
        convertToLogicElement(whileS.getGuardExpression());
    }

    public Modality modus(PosInOccurrence pos) {
        return (Modality) getModalityTerm(pos).op();
    }
    
    private Term getModalityTerm(PosInOccurrence pos) {
        Term progFormula = pos.constrainedFormula().formula();
        
        
        while (progFormula.op() instanceof QuanUpdateOperator) {
            progFormula = ((QuanUpdateOperator)progFormula.op()).target(progFormula);
        }
        return progFormula;
    }
    
    private While getWhileStatement(RuleApp app) {
        final ProgramElement prg = 
            getModalityTerm(app.posInOccurrence()).javaBlock().program();
        
        return (While)((StatementBlock)prg).getFirstActiveChildPos().getProgram(prg);
    }
    
    
    private void createUseCaseBranch(Modality modus, HoareLoopInvRuleApp ruleApp, Goal goal) {
        removeContextFormulas(goal);

        final Services services = goal.proof().getServices();
        final TermBuilder tb = TermBuilder.DF;
        
        Term loopCondition = getCondition(ruleApp, services);

        if (loopCondition.sort() != Sort.FORMULA) {
            loopCondition = tb.equals(loopCondition, tb.FALSE(services));
        } else {
            loopCondition = tb.not(loopCondition);
        }
        
        final Term inv = ruleApp.getInvariant();
        
        Term progFormula = ruleApp.posInOccurrence().constrainedFormula().formula();        
        
        while (progFormula.op() instanceof QuanUpdateOperator) {
            progFormula = ((QuanUpdateOperator)progFormula.op()).target(progFormula);
        }
                
        assert progFormula.op() instanceof Modality;
                
        final ProgramElement prg = progFormula.javaBlock().program();
        
        final PosInProgram whileIdx = ((StatementBlock)prg).getFirstActiveChildPos();
        
        assert whileIdx.last() == 0;
        
        
        LinkedList statementList = new LinkedList();

        PosInProgram idx = whileIdx;

        while (idx != PosInProgram.TOP && 
                idx.up().getProgram(prg) instanceof NonTerminalProgramElement) {

            idx = idx.up();

            final NonTerminalProgramElement ntpe = (NonTerminalProgramElement) idx.getProgram(prg);
                        
            for (int i = 1; i<ntpe.getChildCount(); i++) {
                statementList.add(ntpe.getChildAt(i));
            }
        }
        
        final JavaBlock programTail;

        if (statementList.isEmpty()) {
            programTail = JavaBlock.createJavaBlock(new StatementBlock());
        } else if (statementList.size() > 1 || !(statementList.getFirst() instanceof StatementBlock)) {
            programTail = JavaBlock.createJavaBlock(new StatementBlock(new ArrayOfStatement(statementList)));
        } else {
            programTail = JavaBlock.createJavaBlock((StatementBlock) statementList.getFirst());             
        }
        
        goal.addFormula(new ConstrainedFormula(tb.and(inv, loopCondition)), true, true);
        
        Term useCaseFormula =
            tb.tf().createProgramTerm(modus, programTail, progFormula.sub(0));

        if (modus == Op.DIATRC) {
            useCaseFormula = increaseExecutionTime(goal, services, useCaseFormula);
        }
        
        goal.addFormula(new ConstrainedFormula(useCaseFormula, ruleApp.constraint()), false, true);
        
        goal.setBranchLabel("Use Invariant");
    }

    private Term increaseExecutionTime(Goal goal, final Services services, Term useCaseFormula) {
        final TermBuilder tb = TermBuilder.DF;
        final UpdateFactory uf = new UpdateFactory(services, goal.simplifier());

        final Function execTimeF = 
            (Function) services.getNamespaces().functions().lookup(EXECTIME);
        Term execTime = tb.func(execTimeF);


        final Function addF = 
            services.getTypeConverter().getIntegerLDT().getArithAddition();

        useCaseFormula = 
            uf.apply(uf.elementaryUpdate(execTime, 
                    tb.func(addF, execTime, tb.one(services))), useCaseFormula);
        return useCaseFormula;
    }
    
    private void createPreservesBranch(Modality modus, HoareLoopInvRuleApp ruleApp, Goal goal) {
               
        removeContextFormulas(goal);
        
        Term inv = ruleApp.getInvariant();

        final Services services = goal.proof().getServices();
        final TermBuilder tb = TermBuilder.DF;
        
        Term loopCondition = getCondition(ruleApp, services);

        if (loopCondition.sort() != Sort.FORMULA) {
            loopCondition = tb.equals(loopCondition, tb.TRUE(services));
        }
                
        goal.addFormula(new ConstrainedFormula(tb.and(inv, loopCondition)), true, true);
                
        
        if (modus == Op.DIA || modus == Op.DIATRC) {
            final Term decreasesTerm = ruleApp.getDecreases();
            
            final Metavariable[] mvs = decreasesTerm.metaVars().toArray();
                                   
            final Function oldDecreasesFunc = 
                new RigidFunction(ruleApp.getDecreaseAtPreFuncName(), 
                        decreasesTerm.sort(), toSorts(mvs));
            
            goal.proof().getServices().getNamespaces().functions().add(oldDecreasesFunc);
            
            Term oldDecreases = tb.func(oldDecreasesFunc, toTerms(mvs));
           
            final Term atPreAx = tb.equals(oldDecreases, 
                    decreasesTerm);
            goal.addFormula(new ConstrainedFormula(atPreAx, ruleApp.constraint()), true, true);            

            inv = tb.and(inv, 
                    tb.and(tb.lt(decreasesTerm, oldDecreases, services), 
                            tb.geq(decreasesTerm,tb.zero(services), services)));
        }

        JavaProgramElement loopBody = (JavaProgramElement) getWhileStatement(ruleApp).getBody(); 
        
        if (!(loopBody instanceof StatementBlock)) {
            loopBody = new StatementBlock((Statement)loopBody);
        }               
        
        Term loopFormula = tb.tf().
            createProgramTerm(modus, JavaBlock.createJavaBlock((StatementBlock) loopBody), inv);
      
        if (modus == Op.DIATRC) {
            loopFormula = increaseExecutionTime(goal, services, loopFormula);
        }
        
        goal.addFormula(new ConstrainedFormula(loopFormula, ruleApp.constraint()), false, true);     
        
        goal.setBranchLabel("Preserves Invariant");
    }

    private Term[] toTerms(Metavariable[] mvs) {
        final Term[] mvTerms = new Term[mvs.length];
        for (int i = 0; i<mvTerms.length; i++) {
            mvTerms[i] = TermBuilder.DF.var(mvs[i]);
        }
        return mvTerms;
    }

    private Sort[] toSorts(Metavariable[] mvs) {
        final Sort[] mvSorts = new Sort[mvs.length];
        for (int i = 0; i<mvSorts.length; i++) {
            mvSorts[i] =mvs[i].sort();
        }
        return mvSorts;
    }

    private void removeContextFormulas(Goal goal) {
        final IteratorOfConstrainedFormula itAntec = goal.sequent().antecedent().iterator();        
        while (itAntec.hasNext()) {
            goal.removeFormula(new PosInOccurrence(itAntec.next(), PosInTerm.TOP_LEVEL, true));
        }
                
        final IteratorOfConstrainedFormula itSucc = goal.sequent().succedent().iterator();
        while (itSucc.hasNext()) {
            goal.removeFormula(new PosInOccurrence(itSucc.next(), PosInTerm.TOP_LEVEL, false));
        }
    }

    private void createInitialBranch(Modality modus, HoareLoopInvRuleApp ruleApp, Goal goal) {
        final ConstrainedFormula cf = ruleApp.posInOccurrence().constrainedFormula();
        
        Term formula = cf.formula();       
       
        Term inv = ruleApp.getInvariant();
        
        final UpdateFactory uf = new UpdateFactory(goal.proof().getServices(), goal.simplifier());        

        final Services services = goal.proof().getServices();
        
        if (modus == Op.DIA || modus == Op.DIATRC) {
            inv = TermBuilder.DF.and(inv, 
                    TermBuilder.DF.geq(ruleApp.getDecreases(), TermBuilder.DF.zero(services), services)); 
        }
        
        inv = prependUpdatePrefix(formula, inv, uf);
                
        goal.removeFormula(ruleApp.posInOccurrence());
        goal.addFormula(new ConstrainedFormula(inv, 
                ruleApp.constraint()), false, true);
        goal.setBranchLabel("Invariant Initially Valid");
                
    }

    private Term prependUpdatePrefix(Term formula, Term inv, UpdateFactory uf) {
        
        if (formula.op() instanceof QuanUpdateOperator) {
            return uf.prepend(Update.createUpdate(formula), 
                    prependUpdatePrefix(((QuanUpdateOperator)formula.op()).target(formula), inv, uf));
        }
        return inv;
    }

    
    public String displayName() {        
        return "Loop Invariant";
    }

    public Name name() {
        return LOOP_INV_RULENAME;
    }

    public String toString() {
        return displayName();
    }
    
}
