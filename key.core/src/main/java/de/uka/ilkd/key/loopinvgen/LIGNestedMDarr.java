package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopSpecification;
import org.key_project.util.collection.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class LIGNestedMDarr extends AbstractLoopInvariantGenerator {
//	private final DependenciesLDT depLDT;
//	private final HeapLDT heapLDT;

    public LIGNestedMDarr(Sequent sequent, Services services) {
        super(sequent, services);
        getIndexes(sequent);
//		depLDT = services.getTypeConverter().getDependenciesLDT();
//		heapLDT = services.getTypeConverter().getHeapLDT();
    }

    public LIGNestedMDarr(Sequent sequent, Services services, List<LocationVariable> indexes, int nrArrays) {
        super(sequent, services, indexes, nrArrays);
    }

    public LoopInvariantGenerationResult generate() {
        initialization();

        ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());


        outerCompPreds.add(tb.geq(indexOuter, lowOuter));
//		outerCompPreds.add(tb.geq(indexOuter, tb.add(lowOuter, tb.one())));
//		outerCompPreds.add(tb.geq(indexOuter, tb.sub(lowOuter, tb.one())));
        outerCompPreds.add(tb.leq(indexOuter, highOuter));
//		outerCompPreds.add(tb.leq(indexOuter, tb.add(highOuter, tb.one())));
//		outerCompPreds.add(tb.leq(indexOuter, tb.sub(highOuter, tb.one())));


        outerCompPreds.add(tb.geq(indexInner, lowInner));
//		outerCompPreds.add(tb.geq(indexInner, tb.add(lowInner, tb.one())));
//		outerCompPreds.add(tb.geq(indexInner, tb.sub(lowInner, tb.one())));
        outerCompPreds.add(tb.leq(indexInner, highInner));
//		outerCompPreds.add(tb.leq(indexInner, highInner));
//		outerCompPreds.add(tb.leq(indexInner, tb.sub(highInner, tb.one())));

        outerCompPreds.add(tb.wellFormedMatrix(arrays[0], tb.getBaseHeap()));

        outerDepPreds.add(tb.noR(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        outerDepPreds.add(tb.noW(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        outerDepPreds.add(tb.noW(tb.arrayRange(arrays[0], tb.zero(), tb.sub(tb.dotLength(arrays[0]), tb.one()))));


        innerCompPreds.add(tb.geq(indexOuter, lowOuter));
//		innerCompPreds.add(tb.geq(indexOuter, tb.add(lowOuter, tb.one())));
//		innerCompPreds.add(tb.geq(indexOuter, tb.sub(lowOuter, tb.one())));
//		innerCompPreds.add(tb.leq(indexOuter, highOuter));
        innerCompPreds.add(tb.leq(indexOuter, highOuter));
//		innerCompPreds.add(tb.leq(indexOuter, tb.sub(highOuter, tb.one())));


        innerCompPreds.add(tb.geq(indexInner, lowInner));
//		innerCompPreds.add(tb.geq(indexInner, tb.add(lowInner, tb.one())));
//		innerCompPreds.add(tb.geq(indexInner, tb.sub(lowInner, tb.one())));
        innerCompPreds.add(tb.leq(indexInner, highInner));
//		innerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));
//		innerCompPreds.add(tb.leq(indexInner, tb.sub(highInner, tb.one())));


        innerCompPreds.add(tb.wellFormedMatrix(arrays[0], tb.getBaseHeap()));


        innerDepPreds.add(tb.noR(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        innerDepPreds.add(tb.noW(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        innerDepPreds.add(tb.noW(tb.arrayRange(arrays[0], tb.zero(), tb.sub(tb.dotLength(arrays[0]), tb.one()))));


        int outerItrNumber = -1;
        PredicateRefiner prInner = null;
        prInner = new LoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                innerDepPreds, innerCompPreds, indexOuter, indexInner, outerItrNumber, services);
//		if(arrays.length==1)
//			prInner = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
//					innerDepPreds, innerCompPreds, arrays[0], arrays[0],
//					indexOuter, indexInner, outerItrNumber, services);
//		if(arrays.length==2)
//				prInner = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
//						innerDepPreds, innerCompPreds, arrays[0], arrays[1],
//						indexOuter, indexInner, outerItrNumber, services);
        Pair<Set<Term>, Set<Term>> refinedInnerPreds = prInner.refine();
        innerDepPreds = refinedInnerPreds.first;
        innerCompPreds = refinedInnerPreds.second;

        PredicateRefiner prOuter = null;
        prOuter = new LoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                outerDepPreds, outerCompPreds, indexOuter, indexInner, outerItrNumber, services);

//		if(arrays.length==1)
//			prOuter = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
//					outerDepPreds, outerCompPreds, arrays[0], arrays[0],
//					indexOuter, indexInner, outerItrNumber, services);
//		if(arrays.length==2)
//			prOuter = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
//					outerDepPreds, outerCompPreds, arrays[0], arrays[1],
//					indexOuter, indexInner, outerItrNumber, services);
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
//			System.out.println("Goal after Shifting Outer Loop's Updates: " + goalsAfterShiftUpdate.head());
            for (Goal g : goalsAfterShiftUpdate) {
                for (final SequentFormula sf : g.sequent().succedent()) {
                    final Term formula = tb.goBelowUpdates(sf.formula());
                    if (formula.op() instanceof Modality mod && mod.kind() == Modality.JavaModalityKind.DIA) {
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
                            if (firstApproach && !once) {
                                innerLoop = (LoopStatement) activePE;
                                SideProof innerLoopProof = new SideProof(services, modifySeqAnte(g));
                                innerLI = innerLIComputation(innerLoopProof.retGoal().head(), activePE);//For now only taking the head goal
//								System.out.println("Inner Loop Inv:   " + innerLI);
                                once = true;
                            } else if (!firstApproach) {
                                innerLoop = (LoopStatement) activePE;
                                SideProof innerLoopProof = new SideProof(services, modifySeqFor2ndApproach(g));
                                innerLI = innerLIComputation(innerLoopProof.retGoal().head(), activePE);//For now only taking the head goal
//								System.out.println("2nd Approach Inner Loop Inv:   " + innerLI);
                            }
                        }
                        break;
                    }
                }


                if (nested) {
                    LoopSpecification loopSpec = new LoopSpecificationImpl(innerLoop, tb.and(innerLI.getConjuncts()));
                    services.getSpecificationRepository().addLoopInvariant(loopSpec);
//					System.out.println("Goals before Usecase: " + goalsAfterShiftUpdate.head());
                    ImmutableList<Goal> goalsAfterNestedLoopUsecase = ruleApp.applyNestedLoopUsecaseRule(goalsAfterShiftUpdate);
//					System.out.println("Goals after nested Loop Usecase: "+ goalsAfterNestedLoopUsecase);
                    goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterNestedLoopUsecase);
//					System.out.println("Goals After Shifting the inner LI : " + goalsAfterShift);
                }
                if (firstApproach) {
                    nested = false;
                }
            }
            currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
            System.out.println("Refinement for outer loop: " + " ------------------------------");
            PredicateRefiner prOuter1 = null;
//			if(arrays.length==1)
            prOuter1 = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(),
                    outerDepPreds, outerCompPreds,
                    indexOuter, indexInner, outerItrNumber, services);
//			if(arrays.length==2)
//				prOuter1 = new NestedLoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(),
//						outerDepPreds, outerCompPreds, arrays[0], arrays[1],
//						indexOuter, indexInner, outerItrNumber, services);
            Pair<Set<Term>, Set<Term>> refinedOuterPreds1 = prOuter1.refine();

            outerDepPreds = refinedOuterPreds1.first;
            outerCompPreds = refinedOuterPreds1.second;

        } while ((!outerCompPreds.equals(oldOuterCompPreds) || !outerDepPreds.equals(oldOuterDepPreds)) || outerItrNumber < 2);

        outerDepPreds.addAll(outerCompPreds);

        PredicateSetCompressor compressor =
                new PredicateSetCompressor(outerDepPreds, currentGoal.sequent(), false, services);
        outerDepPreds = compressor.compress();
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
        getHighs(seq);
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


        LIGNewInner innerLIG = new LIGNewInner(newSeq, services, innerDepPreds, innerCompPreds, indexOuter, indexInner, arrays.length);

        return innerLIG.generate();
    }

    private Sequent modifySeqFor2ndApproach(Goal g) {

//		SemisequentChangeInfo semiSCI = new SemisequentChangeInfo(g.sequent().antecedent().asList());
        Sequent newSeq = Sequent.createSequent(g.sequent().antecedent(), g.sequent().succedent());

//		System.out.println("seq for calculating the inner loop inv: " + newSeq);
        return newSeq;
    }
}
