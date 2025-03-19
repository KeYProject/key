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

public class LIGNestedMltpArr extends AbstractLoopInvariantGenerator {
//	private final DependenciesLDT depLDT;
//	private final HeapLDT heapLDT;

    public LIGNestedMltpArr(Sequent sequent, Services services) {
        super(sequent, services);
//		depLDT = services.getTypeConverter().getDependenciesLDT();
//		heapLDT = services.getTypeConverter().getHeapLDT();
    }

    public LoopInvariantGenerationResult generate() {
        initialization();

        ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());

        outerCompPreds.add(tb.geq(indexOuter, lowOuter));
        outerCompPreds.add(tb.geq(indexOuter, tb.add(lowOuter, tb.one())));
        outerCompPreds.add(tb.geq(indexOuter, tb.sub(lowOuter, tb.one())));
        outerCompPreds.add(tb.leq(indexOuter, highOuter));
        outerCompPreds.add(tb.leq(indexOuter, tb.add(highOuter, tb.one())));
        outerCompPreds.add(tb.leq(indexOuter, tb.sub(highOuter, tb.one())));


        outerCompPreds.add(tb.geq(indexInner, lowInner));
        outerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));
        outerCompPreds.add(tb.geq(indexInner, lowInner));
        outerCompPreds.add(tb.geq(indexInner, tb.add(lowInner, tb.one())));
        outerCompPreds.add(tb.geq(indexInner, tb.sub(lowInner, tb.one())));
        outerCompPreds.add(tb.leq(indexInner, highInner));
        outerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));
        outerCompPreds.add(tb.leq(indexInner, tb.sub(highInner, tb.one())));


        outerDepPreds.add(tb.noR(tb.arrayRange(arrays[0], lowOuter, highOuter)));
        outerDepPreds.add(tb.noW(tb.arrayRange(arrays[0], lowOuter, highOuter)));
        outerDepPreds.add(tb.noR(tb.arrayRange(arrays[1], lowInner, highInner)));
        outerDepPreds.add(tb.noW(tb.arrayRange(arrays[1], lowInner, highInner)));

        innerCompPreds.add(tb.geq(indexInner, lowInner));
        innerCompPreds.add(tb.geq(indexInner, tb.add(lowInner, tb.one())));
        innerCompPreds.add(tb.geq(indexInner, tb.sub(lowInner, tb.one())));
        innerCompPreds.add(tb.leq(indexInner, highInner));
        innerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));
        innerCompPreds.add(tb.leq(indexInner, tb.sub(highInner, tb.one())));

        innerDepPreds.add(tb.noR(tb.arrayRange(arrays[0], lowOuter, highOuter)));
        innerDepPreds.add(tb.noW(tb.arrayRange(arrays[0], lowOuter, highOuter)));
        innerDepPreds.add(tb.noR(tb.arrayRange(arrays[1], lowInner, highInner)));
        innerDepPreds.add(tb.noW(tb.arrayRange(arrays[1], lowInner, highInner)));

        int outerItrNumber = -1;
        PredicateRefiner prInner =
                new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                        innerDepPreds, innerCompPreds, arrays[0], arrays[1],
                        indexOuter, indexInner, outerItrNumber, services);
        Pair<Set<Term>, Set<Term>> refinedInnerPreds = prInner.refine();
        innerDepPreds = refinedInnerPreds.first;
        innerCompPreds = refinedInnerPreds.second;

        PredicateRefiner prOuter = new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
                outerDepPreds, outerCompPreds, arrays[0], arrays[1],
                indexOuter, indexInner, outerItrNumber, services);
        Pair<Set<Term>, Set<Term>> refinedOuterPreds = prOuter.refine();
        outerDepPreds = refinedOuterPreds.first;
        outerCompPreds = refinedOuterPreds.second;
//		System.out.println("Outer Comp Preds" + outerCompPreds.toString());
        Goal currentGoal = null;
        boolean once = false; //In the first approach the inner loop's invariant should only be calculated once
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
//			System.out.println("Goals after unwind no "+outerItrNumber+" and BEFORE generationg inner LI: "+ goalsAfterUnwind);

            boolean nested = false;
            boolean firstApproach = true; //First approach forgets everything that it knows. Only produces the inner LI once and uses it.
            // Second approach calculates th inner LI for each outer iteration.
            // I should compare their speed and precision.
            ImmutableList<Goal> goalsAfterShiftUpdate = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
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
                            System.out.println("Nested Loop!");
                            nested = true;//Even if the loop is not nested the modality starts with a While. I should find another way to distinguish between nested and normal loops
                            if (!once) {
                                innerLoop = (LoopStatement) activePE;
                                SideProof innerLoopProof = new SideProof(services, modifySeq(g));
                                innerLI = innerLIComputation(innerLoopProof.retGoal().head(), outerItrNumber, activePE);//For now only taking the head goal
                                System.out.println("Inner Loop Inv:   " + innerLI);
                                once = true;
                            }
                        }
                        break;
                    }
                }

//				System.out.println("Goals after unwind, generating Inner LI and shift no "+outerItrNumber +" : "+ goalsAfterShiftUpdate.head());

                if (nested && firstApproach) {
                    nested = false;
                    LoopSpecification loopSpec = new LoopSpecificationImpl(innerLoop, tb.and(innerLI.getConjuncts()));
                    services.getSpecificationRepository().addLoopInvariant(loopSpec);
//					System.out.println("Goals before Usecase: " + goalsAfterShiftUpdate.head());
                    ImmutableList<Goal> goalsAfterNestedLoopUsecase = ruleApp.applyNestedLoopUsecaseRule(goalsAfterShiftUpdate);
//					System.out.println("Goals after nested Loop Usecase: "+ goalsAfterNestedLoopUsecase);
                    goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterNestedLoopUsecase);
//					System.out.println("Goals After Shifting the inner LI : " + goalsAfterShift);
//
                }
            }
//			outerDepPreds = innerDepPreds;//because I also gave the inner inv generator the outer arrays dep predicates
            currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
//			System.out.println("goal for refinement: " + currentGoal + " ------------------------------");
            PredicateRefiner prOuter1 =
                    new NestedLoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(),
                            outerDepPreds, outerCompPreds, arrays[0], arrays[1],
                            indexOuter, indexInner, outerItrNumber, services);
            Pair<Set<Term>, Set<Term>> refinedOuterPreds1 = prOuter1.refine();
//		System.out.println(ProofSaver.printAnything(seq, services));
            outerDepPreds = refinedOuterPreds1.first;
            outerCompPreds = refinedOuterPreds1.second;


        } while ((!outerCompPreds.equals(oldOuterCompPreds) || !outerDepPreds.equals(oldOuterDepPreds)) || outerItrNumber < 2);

        outerDepPreds.addAll(outerCompPreds);

//		PredicateSetCompressor compressor =
//				new PredicateSetCompressor(outerDepPreds, currentGoal.sequent(), false, services);
//		outerDepPreds = compressor.compress();
        LoopInvariantGenerationResult outLoopInv = new LoopInvariantGenerationResult(outerDepPreds, outerItrNumber, services);
        System.out.println("Outer loops invariant: " + outLoopInv.toString());
        return outLoopInv;
    }

    private Sequent modifySeq(Goal g) {
//		System.out.println("Goal before modifySeq: "+ g);
        Set<Term> initialFormulas = new HashSet<>();
        initialFormulas.add(tb.geq(indexInner, lowInner));
        initialFormulas.add(tb.leq(indexInner, tb.add(highInner, tb.one())));

//		for (Term arr : arrays) {
        initialFormulas.add(tb.noR(tb.arrayRange(arrays[0], lowInner, highInner)));
        initialFormulas.add(tb.noW(tb.arrayRange(arrays[0], lowInner, highInner)));
        initialFormulas.add(tb.noR(tb.arrayRange(arrays[1], lowOuter, highOuter)));
        initialFormulas.add(tb.noW(tb.arrayRange(arrays[1], lowOuter, highOuter)));

//		}
        SequentFormula newAnteFrm = new SequentFormula(tb.and(initialFormulas));
//		SemisequentChangeInfo semiSCI = new SemisequentChangeInfo(g.sequent().antecedent().asList());
        Sequent newSeq = Sequent.createSequent(new Semisequent(newAnteFrm), g.sequent().succedent());
//		System.out.println("Goal after modifySeq: "+ g);
//		System.out.println("seq for calculating the inner loop inv: " + newSeq);
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


    private LoopInvariantGenerationResult innerLIComputation(Goal g, int itrNumber, Statement activePE) {
        System.out.println("Entered innerLIComputation");

        StatementBlock stmtBlck = new StatementBlock(activePE);
        JavaBlock jb = JavaBlock.createJavaBlock(stmtBlck);

        Term delta = tb.ff();
        for (SequentFormula sf : g.sequent().succedent()) {
            if (!sf.formula().containsJavaBlockRecursive()) {
                delta = tb.or(delta, sf.formula());
            }
        }

        Term newDiamond = tb.dia(jb, tb.tt()); //"tb.tt()" should be the post condition we want to prove

        SequentFormula succSF = new SequentFormula(tb.or(newDiamond, delta));
        Semisequent succSemi = new Semisequent(succSF);

        Sequent newSeq = Sequent.createSequent(g.sequent().antecedent(), succSemi);

//				System.out.println("New Seq for inner loop:  "+ newSeq);

        Set<Term> allDepPreds = innerDepPreds;

        allDepPreds.addAll(outerDepPreds);//added for having multiple arrays

        LIGNewInnerMltpArr innerLIG = new LIGNewInnerMltpArr(newSeq, services, allDepPreds, innerCompPreds, arrays[0], arrays[1], indexOuter, indexInner);
        LoopInvariantGenerationResult loopInvariantGenerationResult = innerLIG.generate();

        return loopInvariantGenerationResult;
    }
}
