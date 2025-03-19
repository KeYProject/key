package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.NameAbstractionTable;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.util.Pair;
import org.jetbrains.annotations.NotNull;
import org.key_project.util.collection.ImmutableList;

import java.util.HashSet;
import java.util.Set;

public class NestedLIGNewRelaxed extends AbstractLoopInvariantGenerator {
    //	protected Term indexOuter;
//	protected Term lowOuter;
//	protected Term highOuter;
//	protected Term indexInner;
//	protected Term lowInner;
//	protected Term highInner;
//
//	protected Term[][] arrays = new Term[1][];
    private final LoopStatement outerLoop;

    public NestedLIGNewRelaxed(Sequent sequent, Term formula, Services services) {
        super(sequent, services);
        this.outerLoop = (LoopStatement) JavaTools.getActiveStatement(TermBuilder.goBelowUpdates(formula).javaBlock());
        initialization();
    }

    public NestedLIGNewRelaxed(Sequent sequent, LoopStatement loopStatement, Services services, Term[] arrays, Term outI, Term outL, Term outH, Term inI, Term inL, Term inH) {
        super(sequent, services);
        this.outerLoop = loopStatement;

        this.arrays = arrays;

        this.indexOuter = outI;
        this.highOuter = outH;
        this.lowOuter = outL;

        this.indexInner = inI;
        this.lowInner = inL;
        this.highInner = inH;
    }

    @Override
    public LoopInvariantGenerationResult generate() {

        System.out.println("Relaxed LIG:  ");

        for (SequentFormula sf : seq.antecedent()) {
            if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
                allCompPreds.add(sf.formula());
            }
        }
        for (SequentFormula sf : seq.succedent()) {
            if (!sf.formula().containsJavaBlockRecursive() && isComparisonOperator(sf.formula())) {
                allCompPreds.add(tb.not(sf.formula()));
            }
        }

        allCompPreds = filterOutTimeStamp(allCompPreds);

        ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
//		System.out.println("SHIFTED");
//		System.out.println("number of goals after shift number -1: " + goalsAfterShift.size());// It is always one
//		System.out.println(
//				"Goals after shift -1: " + ProofSaver.printAnything(goalsAfterShift.head().sequent(), services));

        Goal currentGoal = goalsAfterShift.head();// Number of goals after shift does not change

        allCompPreds.add(tb.geq(indexOuter, lowOuter));
        allCompPreds.add(tb.leq(indexOuter, tb.add(highOuter, tb.one())));
        allCompPreds.add(tb.geq(indexInner, lowInner));
        allCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));

//		allCompPreds.add(tb.equals(indexInner, tb.zero()));

        allCompPreds.add(tb.wellFormedMatrix(arrays[0], tb.getBaseHeap()));

        allDepPreds.add(tb.relaxedNoR(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        allDepPreds.add(tb.relaxedNoW(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        allDepPreds.add(tb.relaxedNoW(tb.arrayRange(arrays[0], tb.zero(), tb.sub(tb.dotLength(arrays[0]), tb.one()))));


        int itrNumber = -1;
        PredicateRefiner pr0 = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(), allDepPreds, allCompPreds, indexOuter,
                indexInner, itrNumber, services);
        Pair<Set<Term>, Set<Term>> refinedPreds = pr0.refine();
//		System.out.println(ProofSaver.printAnything(seq, services));
        allDepPreds = refinedPreds.first;
        allCompPreds = refinedPreds.second;

//		for (Goal g : goalsAfterShift) {
//			g = abstractGoal(g);
//		}

        do {
            itrNumber++;
            System.out.println("Iteration Number: " + itrNumber);

            oldDepPreds.clear();
            oldCompPreds.clear();

            oldDepPreds.addAll(allDepPreds);
            oldCompPreds.addAll(allCompPreds);

//			System.out.println("BEFORE UNWIND");
//			System.out.println(goalsAfterShift);
//			System.out.println("Goals Before Unwind:" + goalsAfterShift);

            ImmutableList<Goal> goalsAfterUnwind = ruleApp.applyLoopScopeUnwindRule(goalsAfterShift);
//			System.out.println("AFTER UNWIND");
//			System.out.println("Number of goals after unwind: " + goalsAfterUnwind.size());
//			System.out.println("Goals After Unwind:" + goalsAfterUnwind);
//			System.out.println(goalsAfterUnwind);
            goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
//			System.out.println("SHIFT");
//			System.out.println("Number of goals after shift: " + goalsAfterShift.size());
//			System.out.println("Goals After Shift:" + goalsAfterShift);

            currentGoal = ruleApp.findLoopScopeLoopUnwindTacletGoal(goalsAfterShift);

//			System.out.println("Current Goal: " + currentGoal);
//			currentIndexFormula = currentIndexEq(currentGoal.sequent(), index);
//			System.out.println("Before refinement: " + currentGoal.sequent());

            LoopStatement ls = ruleApp.getLoopStatementFromGoal(currentGoal);
            if (!(ls.equalsModRenaming(outerLoop, new NameAbstractionTable()))) {
                System.out.println("Inner Loop detected");
                Sequent innerSeq = modifySeq(currentGoal, ls);

                NestedLIGNewRelaxed innerLoopGen = new NestedLIGNewRelaxed(innerSeq, ls, services, arrays, indexOuter, lowOuter, highOuter, indexInner, lowInner, highInner);

                LoopInvariantGenerationResult result = innerLoopGen.generate();

//				Set<Term> conjuncts = filterConjuncts(result);
//				System.out.println("CONJUNCTS:  " + conjuncts);

                LoopSpecification loopSpec = new LoopSpecificationImpl(ls, tb.and(result.getConjuncts()));

                services.getSpecificationRepository().addLoopInvariant(loopSpec);

//				System.out.println("============Goals After Shift============ " + goalsAfterShift);
                ImmutableList<Goal> goalsAfterInnerLoop = ruleApp.applyNestedLoopUsecaseRule(goalsAfterShift);
//				System.out.println("============Goals After Inner Loop============ " + goalsAfterInnerLoop);

                currentGoal = ruleApp.findLoopUnwindTacletGoal(ruleApp.applyShiftUpdateRule(goalsAfterInnerLoop));
            }


            PredicateRefiner pr = new LoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(), allDepPreds, allCompPreds, indexOuter,
                    indexInner, itrNumber, services);
            refinedPreds = pr.refine();
            allDepPreds = refinedPreds.first;
            allCompPreds = refinedPreds.second;

            allCompPreds = filterOutTimeStamp(allCompPreds);

//			currentGoal = abstractGoal(currentGoal);
            for (Goal g : goalsAfterShift) {
                abstractGoal(g, allCompPreds, allDepPreds);
            }
//			System.out.println("Dep Preds: " + allDepPreds);
        } while ((!allCompPreds.equals(oldCompPreds) || !allDepPreds.equals(oldDepPreds)) || itrNumber < 2);

        allDepPreds.addAll(allCompPreds);

        final PredicateSetCompressor compressor =
                new PredicateSetCompressor(allDepPreds, currentGoal.sequent(), false, services);
        allDepPreds = compressor.compress();

        LoopInvariantGenerationResult result = new LoopInvariantGenerationResult(allDepPreds, itrNumber, services);


        System.out.println("Loop Invariant is: " + result);
        return result;
    }

    @NotNull
    private Set<Term> filterConjuncts(LoopInvariantGenerationResult result) {
        Set<Term> conjuncts = new HashSet<>();
        for (Term conjunct : result.getConjuncts()) {
            OpCollector collector = new OpCollector();
            conjunct.execPostOrder(collector);
            //collector.ops()
            if (!collector.contains(services.getTypeConverter().getDependenciesLDT().getTimestamp())) {
                conjuncts.add(conjunct);
            }
        }
        return conjuncts;
    }

    private Set<Term> filterOutTimeStamp(Set<Term> comPreds) {
        Set<Term> res = new HashSet<>();
        for (Term c : comPreds) {
            OpCollector collector = new OpCollector();
            c.execPostOrder(collector);
            //collector.ops()
            if (!collector.contains(services.getTypeConverter().getDependenciesLDT().getTimestamp())) {
                res.add(c);
            }
        }
        return res;
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


    private Sequent modifySeq(Goal g, LoopStatement innerLoop) {
//		System.out.println("Modified Ante start");
        Set<Term> initialFormulas = new HashSet<>();
//		initialFormulas.add(tb.geq(indexInner, lowInner));
//		initialFormulas.add(tb.leq(indexInner, tb.add(highInner, tb.one())));

//		for (Term arr : arrays) {
//			initialFormulas.add(tb.relaxedNoR(tb.arrayRange(arr, lowInner, highInner)));
//			initialFormulas.add(tb.relaxedNoW(tb.arrayRange(arr, lowInner, highInner)));
//		}


        initialFormulas.add(tb.relaxedNoR(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        initialFormulas.add(tb.relaxedNoW(tb.matrixRange(tb.getBaseHeap(), arrays[0], lowOuter, highOuter, lowInner, highInner)));
        initialFormulas.add(tb.relaxedNoW(tb.arrayRange(arrays[0], tb.zero(), tb.sub(tb.dotLength(arrays[0]), tb.one()))));

        Semisequent newAntecedent = filterSemisequent(g.sequent().antecedent());
        SequentFormula newAnteFrm = new SequentFormula(tb.and(initialFormulas));
        newAntecedent = newAntecedent.insertFirst(newAnteFrm).semisequent();

        Semisequent newSuccedent = filterSemisequent(g.sequent().succedent());


        Term post = tb.tt();
        Term programFormula = tb.dia(JavaBlock.createJavaBlock(new StatementBlock(innerLoop)), post);
        Sequent newSeq = Sequent.createSequent(newAntecedent,
                newSuccedent.insertFirst(new SequentFormula(programFormula)).semisequent());

//		System.out.println("Modified Ante for the Inner Loop LIG: " + newSeq);
        return newSeq;
    }

    private Semisequent filterSemisequent(Semisequent semisequent) {
        Semisequent filteredSemisequent = Semisequent.EMPTY_SEMISEQUENT;
        DependenciesLDT depLDT = services.getTypeConverter().getDependenciesLDT();

        filter:
        for (SequentFormula sf : semisequent) {

            if (!sf.formula().containsJavaBlockRecursive()) {
                final OpCollector collector = new OpCollector();
                collector.visit(sf.formula());
                for (Operator op : collector.ops()) {
                    if (depLDT.isDependencePredicate(op) || op == depLDT.getTimestamp()) {
                        continue filter;
                    }
                }
                filteredSemisequent = filteredSemisequent.insertFirst(sf).semisequent();
            }
        }
        return filteredSemisequent;
    }

}
