package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopSpecification;
import org.key_project.util.collection.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.Set;

public class LIGNested extends AbstractLoopInvariantGenerator {
//	private final DependenciesLDT depLDT;
//	private final HeapLDT heapLDT;

    public LIGNested(Sequent sequent, Services services) {
        super(sequent, services);
//		depLDT = services.getTypeConverter().getDependenciesLDT();
//		heapLDT = services.getTypeConverter().getHeapLDT();
    }

    public LoopInvariantGenerationResult generate() {
        initialization();

        ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());

        outerCompPreds.add(tb.geq(indexOuter, lowOuter));
        outerCompPreds.add(tb.leq(indexOuter, tb.add(highOuter, tb.one())));
        outerCompPreds.add(tb.geq(indexInner, lowInner));
        outerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));

        outerDepPreds.add(tb.noR(tb.arrayRange(arrays[0], lowOuter, highOuter)));
        outerDepPreds.add(tb.noW(tb.arrayRange(arrays[0], lowOuter, highOuter)));

        innerCompPreds.add(tb.geq(indexInner, lowInner));
        innerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));

        innerDepPreds.add(tb.noR(tb.arrayRange(arrays[0], lowInner, highInner)));
        innerDepPreds.add(tb.noW(tb.arrayRange(arrays[0], lowInner, highInner)));

        int outerItrNumber = -1;
        PredicateRefiner prInner = null;
        if (arrays.length == 1)
            prInner = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                    innerDepPreds, innerCompPreds, arrays[0], arrays[0],
                    indexOuter, indexInner, outerItrNumber, services);
        if (arrays.length == 2)
            prInner = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                    innerDepPreds, innerCompPreds, arrays[0], arrays[1],
                    indexOuter, indexInner, outerItrNumber, services);
        Pair<Set<Term>, Set<Term>> refinedInnerPreds = prInner.refine();
        innerDepPreds = refinedInnerPreds.first;
        innerCompPreds = refinedInnerPreds.second;

        PredicateRefiner prOuter = null;
        if (arrays.length == 1)
            prOuter = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                    innerDepPreds, innerCompPreds, arrays[0], arrays[0],
                    indexOuter, indexInner, outerItrNumber, services);
        if (arrays.length == 2)
            prOuter = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                    innerDepPreds, innerCompPreds, arrays[0], arrays[1],
                    indexOuter, indexInner, outerItrNumber, services);
        Pair<Set<Term>, Set<Term>> refinedOuterPreds = prOuter.refine();
        outerDepPreds = refinedOuterPreds.first;
        outerCompPreds = refinedOuterPreds.second;

        Goal currentGoal;
        boolean once = false; //the inner loop's invariant should only be calculated once in the first approach
        LoopStatement innerLoop = null;
        LoopInvariantGenerationResult innerLI = null;
        do {
            outerItrNumber++;
//			**
            System.out.println("OUTER Iteration Number: " + outerItrNumber);

            oldOuterDepPreds.clear();
            oldOuterCompPreds.clear();

            oldOuterDepPreds.addAll(outerDepPreds);
            oldOuterCompPreds.addAll(outerCompPreds);

            ImmutableList<Goal> goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);


            boolean nested = false;
            boolean firstApproach = false; //First approach forgets everything that it knows. Only produces the inner LI once and uses it.
            // Second approach calculates th inner LI for each outer iteration.
            // I should compare their speed and precision.
            ImmutableList<Goal> goalsAfterShiftUpdate = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);

            for (Goal g : goalsAfterShiftUpdate) {
                for (final SequentFormula sf : g.sequent().succedent()) {
                    final Term formula = tb.goBelowUpdates(sf.formula());
                    if (formula.op() instanceof Modality mod && mod.kind() == JavaModalityKind.DIA) {
                        ProgramElement pe = formula.javaBlock().program();
                        Statement activePE;
                        if (pe instanceof ProgramPrefix) {
                            activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
                        } else {
                            activePE = (Statement) pe.getFirstElement();
                        }
                        if (activePE instanceof While) {
                            // **
                            System.out.println("Nested Loop!");
                            nested = true;//Even if the loop is not nested the modality starts with a While. I should find another way to distinguish between nested and normal loops
                            if (!once) {
                                innerLoop = (LoopStatement) activePE;
                                SideProof innerLoopProof = new SideProof(services, modifySeqAnte(g));
                                innerLI = innerLIComputation(innerLoopProof.retGoal().head(), activePE);//For now only taking the head goal
                                System.out.println("Inner Loop Inv:   " + innerLI);
                                once = true;
                            }
                        }
                        break;
                    }
                }

                if (nested && firstApproach) {
                    nested = false;
                    LoopSpecification loopSpec = new LoopSpecificationImpl(innerLoop, tb.and(innerLI.getConjuncts()));
                    services.getSpecificationRepository().addLoopInvariant(loopSpec);
                    ImmutableList<Goal> goalsAfterNestedLoopUsecase = ruleApp.applyNestedLoopUsecaseRule(goalsAfterShiftUpdate);

                    goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterNestedLoopUsecase);
                }
            }
            currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
//			System.out.println("goal for refinement: " + currentGoal + " ------------------------------");
            PredicateRefiner prOuter1 = null;
            if (arrays.length == 1)
                prOuter1 = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                        innerDepPreds, innerCompPreds, arrays[0], arrays[0],
                        indexOuter, indexInner, outerItrNumber, services);
            if (arrays.length == 2)
                prOuter1 = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                        innerDepPreds, innerCompPreds, arrays[0], arrays[1],
                        indexOuter, indexInner, outerItrNumber, services);
            Pair<Set<Term>, Set<Term>> refinedOuterPreds1 = prOuter1.refine();

            outerDepPreds = refinedOuterPreds1.first;
            outerCompPreds = refinedOuterPreds1.second;

        } while ((!outerCompPreds.equals(oldOuterCompPreds) || !outerDepPreds.equals(oldOuterDepPreds)) || outerItrNumber < 2);

        outerDepPreds.addAll(outerCompPreds);

//		PredicateSetCompressor compressor =
//				new PredicateSetCompressor(outerDepPreds, currentGoal.sequent(), false, services);
//		outerDepPreds = compressor.compress();
        LoopInvariantGenerationResult outLoopInv = new LoopInvariantGenerationResult(outerDepPreds, outerItrNumber, services);
        System.out.println("Outer loops invariant: " + outLoopInv);
        return outLoopInv;
    }

    private Sequent modifySeqAnte(Goal g) {
        Set<Term> initialFormulas = new HashSet<>();
        initialFormulas.add(tb.geq(indexInner, lowInner));
        initialFormulas.add(tb.leq(indexInner, tb.add(highInner, tb.one())));
        for (Term arr : arrays) {
            initialFormulas.add(tb.noR(tb.arrayRange(arr, lowInner, highInner)));
            initialFormulas.add(tb.noW(tb.arrayRange(arr, lowInner, highInner)));
        }

        SequentFormula newAnteFrm = new SequentFormula(tb.and(initialFormulas));
        Sequent newSeq = Sequent.createSequent(new Semisequent(newAnteFrm), g.sequent().succedent());

//		System.out.println("Modified Ante for the Inner Loop LIG: " + newSeq);
        return newSeq;
    }

    private void initialization() {
        getLows(seq);
        getIndexesAndHighs(seq);
        getLocSet(seq);

        for (SequentFormula sf : seq.antecedent()) {
            if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
                innerCompPreds.add(sf.formula());
                outerCompPreds.add(sf.formula());
            }
        }
        for (SequentFormula sf : seq.succedent()) {
            if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
                innerCompPreds.add(tb.not(sf.formula()));
                outerCompPreds.add(tb.not(sf.formula()));
            }
        }
    }

    private LoopInvariantGenerationResult innerLIComputation(Goal g, Statement innerLoop) {
        System.out.println("Entered innerLIComputation");

        StatementBlock stmtBlck = new StatementBlock(innerLoop);
        JavaBlock jb = JavaBlock.createJavaBlock(stmtBlck);

        Term delta = tb.ff();
        for (SequentFormula sf : g.sequent().succedent()) {
            if (!sf.formula().containsJavaBlockRecursive()) {
                delta = tb.or(delta, sf.formula());
            }
        }

        Term newDiamond = tb.dia(jb, tb.tt());

        SequentFormula succSF = new SequentFormula(tb.or(newDiamond, delta));
        Semisequent succSemi = new Semisequent(succSF);

        Sequent newSeq = Sequent.createSequent(g.sequent().antecedent(), succSemi);


        LIGNewInnerMltpArr innerLIG = new LIGNewInnerMltpArr(newSeq, services, innerDepPreds, innerCompPreds, arrays[0], arrays[0], indexOuter, indexInner);

        return innerLIG.generate();
    }
}
