package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.ldt.DependenciesLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Pair;
import org.key_project.util.collection.ImmutableList;

import java.util.*;

public class LIGNested  extends AbstractLoopInvariantGenerator {
	private final DependenciesLDT depLDT;
	private Sequent newSeq;
	private Semisequent newSeqAnte;
	private Semisequent newSeqSucc;

	public LIGNested(Sequent sequent, Services services) {
		super(sequent, services);
		depLDT = services.getTypeConverter().getDependenciesLDT();
	}

	public LoopInvariantGenerationResult generate() {
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


//		System.out.println("Goals before shift number -1: "+services.getProof().openGoals());
		ImmutableList<Goal> goalsAfterShift = ruleApp.applyShiftUpdateRule(services.getProof().openGoals());
//		System.out.println("SHIFTED");
//		System.out.println("number of goals after shift number -1: " + goalsAfterShift.size());// It is always one
//		System.out.println(
//				"Goals after shift -1: " + ProofSaver.printAnything(goalsAfterShift.head().sequent(), services));

		Sequent seqZero = Sequent.createSequent(goalsAfterShift.head().sequent().antecedent(), goalsAfterShift.head().sequent().succedent());

		// Number of goals after shift does not change

//		// Initial Predicate Sets for stencil and conditionalWithDifferentEvents: 
//		allCompPreds.add(tb.geq(index, tb.sub(low,tb.one())));//
//		allCompPreds.add(tb.leq(index, tb.add(high, tb.one())));//
//		for (Term arr : arrays) {
//			allDepPreds.add(tb.noR(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
//			allDepPreds.add(tb.noW(tb.arrayRange(arr, tb.sub(low,tb.one()), high)));
//		}


//		//Initial Predicate Sets for shiftArrayToLeft, shiftArrayToLeftWithBreak, withoutFunc, withFunc, conditionWithDifferentNumberOfEvent, condition:
		outerCompPreds.add(tb.geq(indexOuter, lowOuter));
		outerCompPreds.add(tb.leq(indexOuter, tb.add(highOuter, tb.one())));
		for (Term arr : arrays) {
			outerDepPreds.add(tb.noR(tb.arrayRange(arr, lowOuter, highOuter)));
			outerDepPreds.add(tb.noW(tb.arrayRange(arr, lowOuter, highOuter)));
		}
		innerCompPreds.add(tb.geq(indexInner, lowInner));
		innerCompPreds.add(tb.leq(indexInner, tb.add(highInner, tb.one())));
		for (Term arr : arrays) {
			innerDepPreds.add(tb.noR(tb.arrayRange(arr, lowInner, highInner)));
			innerDepPreds.add(tb.noW(tb.arrayRange(arr, lowInner, highInner)));
		}

		int outerItrNumber = -1;
		PredicateRefiner pr0 =
				new NestedLoopIndexAndDependencyPredicateRefiner(goalsAfterShift.head().sequent(),
						innerDepPreds, innerCompPreds,
						indexOuter, indexInner, outerItrNumber, services);
		Pair<Set<Term>, Set<Term>> refinedPreds = pr0.refine();
//		System.out.println(ProofSaver.printAnything(seq, services));
		innerDepPreds = refinedPreds.first;
		innerCompPreds = refinedPreds.second;
		outerDepPreds = refinedPreds.first;
		outerCompPreds = refinedPreds.second;

		Boolean nested = false;
		//do {
			outerItrNumber++;
//			**		
			System.out.println("OUTER Iteration Number: " + outerItrNumber);

			oldOuterDepPreds.clear();
			oldOuterCompPreds.clear();

			oldOuterDepPreds.addAll(outerDepPreds);
			oldOuterCompPreds.addAll(outerCompPreds);

//			System.out.println("Before UNWIND");
			ImmutableList<Goal> goalsAfterUnwind = ruleApp.applyUnwindRule(goalsAfterShift);
//			System.out.println("UNWIND");
//			System.out.println("Number of goals after unwind: " + goalsAfterUnwind.size());
//			System.out.println("Goals After Unwind:" + goalsAfterUnwind);
			goalsAfterShift = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
//			System.out.println("SHIFT");
//			System.out.println("Number of goals after shift: " + goalsAfterShift.size());
//			System.out.println("Goals After Shift:" + goalsAfterShift);


			Goal currentGoal = ruleApp.findLoopUnwindTacletGoal(goalsAfterShift);
//			System.out.println("Current Goal: " + currentGoal);

			LoopInvariantGenerationResult innerLI = null;
			Term readLocSet = null;
			Term writtenLocSet = null;
			Term rawLocSet = null;
			Term warLocSet = null;
			for (final SequentFormula sf : currentGoal.sequent().succedent()) {
				if (sf.formula().op() == Modality.DIA) {
					ProgramElement pe = sf.formula().javaBlock().program();
					Statement activePE;
					if (pe instanceof ProgramPrefix) {
						activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
					} else {
						activePE = (Statement) pe.getFirstElement();
					}
					if (activePE instanceof While) {
						System.out.println("Nested Loop!");
						nested = true;

						innerLI = innerLIComputation(currentGoal, 0, activePE);
						readLocSet = readLocSets(innerLI);
						writtenLocSet = writtenLocSets(innerLI);
						Term intersectRandW = tb.intersect(readLocSet, writtenLocSet);
						rawLocSet = extractRaWLocs(innerLI, intersectRandW);
						warLocSet = extractWaRLocs(innerLI, intersectRandW);
					}
				}
				break;
			}
			if(nested) {
				nested = false;
				Statement outerLoop = reconstructOuterLoop(seqZero);
//					Term u = constructU(seqZero); //U is shifted and it's in \Gama
				Term wUpdate = constructW(seqZero, readLocSet, writtenLocSet, rawLocSet, warLocSet);
				//apply the usecase of LI rule
				constructUsecase(seqZero, outerLoop, innerLI,wUpdate, currentGoal);
				}
//			currentIndexFormula = currentIndexEq(currentGoal.sequent(), index);
//			System.out.println("Before refinement: " + currentGoal.sequent());
//			PredicateRefiner pr = new NestedLoopIndexAndDependencyPredicateRefiner(currentGoal.sequent(), innerDepPreds, innerCompPreds,
//					indexOuter, indexInner, outerItrNumber, services);
//			refinedPreds = pr.refine();
//			innerDepPreds = refinedPreds.first;
//			innerCompPreds = refinedPreds.second;
//			for (Term t : refinedPreds.first) {
//				System.out.println("refined: " + t);
//			}
////			currentGoal = abstractGoal(currentGoal);
//			for (Goal g : goalsAfterShift) {
////				System.out.println("goal before abstraction: "+g);
//				abstractGoal(g, innerCompPreds, innerDepPreds);
////				System.out.println("goal after abstraction: "+g);
//			}

//			System.out.println("Dep Preds: " + allDepPreds);
		//} while ((!innerCompPreds.equals(oldInnerCompPreds) || !innerDepPreds.equals(oldInnerDepPreds)) || outerItrNumber < 3);

		innerDepPreds.addAll(innerCompPreds);

//		PredicateSetCompressor compressor =
//				new PredicateSetCompressor(innerDepPreds, currentGoal.sequent(), false, services);
//		innerDepPreds = compressor.compress();
		LoopInvariantGenerationResult inLoopInv = new LoopInvariantGenerationResult(innerDepPreds, outerItrNumber);
		System.out.println("Inner loops invariant: " + inLoopInv);
		return null;
	}

	private Goal constructUsecase(Sequent seqZero, Statement outerLoop,LoopInvariantGenerationResult innerLI, Term wUpdate, Goal g) {
		StatementBlock loopBlock = new StatementBlock(outerLoop);
		JavaBlock jb = JavaBlock.createJavaBlock(loopBlock);
		SequentFormula phi=null;
		for(SequentFormula sf:seqZero.succedent()){
			if(sf.formula().op() != Modality.DIA){
				phi=sf;
				System.out.println("Phi is: "+phi);
			}
			break;
		}
		//Succ:
		Term newDiamond = tb.dia(jb, (Term)phi);
		Term newSuccTerm = tb.apply(wUpdate, newDiamond);
		SequentFormula newSuccSF = new SequentFormula(newSuccTerm);

		for(SequentFormula sf:g.sequent().succedent()){
			PosInOccurrence p = new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
			g.removeFormula(p);
		}

		g.addFormula(newSuccSF,false, true);

		//Ante:
		Expression outerLoopGuard = null;
		if(outerLoop instanceof  While){
			outerLoopGuard = ((While) outerLoop).getGuardExpression();
		}
		Term updatedFalseGuard=tb.apply(wUpdate,tb.not((Term)outerLoopGuard));
		g.addFormula((SequentFormula) updatedFalseGuard,true,false);

		for(Term t:innerLI.getConjuncts()) {
			g.addFormula((SequentFormula)tb.apply(wUpdate, t), true, false);
		}

		System.out.println("UseCase goal is: "+ g.sequent());

		return g;
	}


	private Term constructW(Sequent seqZero, Term readLocSet, Term writtenLocSet, Term rawLocSet, Term warLocSet){//assuming loop does not creat new objects
		//readEv, writeEv, readEv
		Term w = null;

		Term readEv1 = tb.anonEventUpdate(rawLocSet, tb.zTerm(2));
		Term writeEv = tb.anonEventUpdate(tb.union(rawLocSet, warLocSet), tb.zTerm(1));
		Term readEv2 = tb.anonEventUpdate(warLocSet, tb.zTerm(0));
		w = tb.sequential(readEv1, tb.sequential(writeEv,readEv2));
		return w;
	}

	private Term extractWaRLocs(LoopInvariantGenerationResult innerLI, Term intersectRandW) {
		Term locSet =null;

		for(Term pred: innerLI.getConjuncts()){
			if (pred.op().equals(depLDT.getNoWaR())){
				locSet = pred.sub(0);
			}
			break;
		}
		System.out.println("noRaW LocSet: "+locSet);

		if(locSet!=null){
			locSet = tb.intersect(locSet, intersectRandW);
		}
		System.out.println("Read and written LocSets but noRaW: " + locSet);

		return locSet;
	}
	private Term extractRaWLocs(LoopInvariantGenerationResult innerLI, Term intersectRandW) {
		Term locSet =null;

		for(Term pred: innerLI.getConjuncts()){
			if (pred.op().equals(depLDT.getNoRaW())){
				locSet = pred.sub(0);
			}
			break;
		}
		System.out.println("noRaW LocSet: "+locSet);

		if(locSet!=null){
			locSet = tb.intersect(locSet, intersectRandW);
		}
		System.out.println("Read and written LocSets but noRaW: " + locSet);

		return locSet;
	}

	private Term readLocSets(LoopInvariantGenerationResult innerLI) {//assuming we have only one noR in the LI and it doesn't have \cap or \cup in it
		Term locSet =null;
		for(Term pred: innerLI.getConjuncts()){
			if (pred.op().equals(depLDT.getNoR())){
				locSet = pred.sub(0);
			}
			break;
		}
		System.out.println("Unread LocSet: "+locSet);

		Set<Term> arr = getInnerLocSets();
		Set<Term> ret = new HashSet<>();
		Term retTerm = null;

		if(locSet!=null){
			for(Term a:arr){
				if(locSet.sub(0)==a.sub(0)) {//Same array
					ret.add(tb.sub(a, locSet));
				}
			}
		}
		retTerm = tb.union(ret);
		System.out.println("Read LocSets is: "+retTerm);

		return retTerm;

	}

	private Term writtenLocSets(LoopInvariantGenerationResult innerLI) {//assuming we have only one noW in the LI and it doesn't have \cap or \cup in it
		Term locSet =null;
		for(Term pred: innerLI.getConjuncts()){
			if (pred.op().equals(depLDT.getNoW())){
				locSet = pred.sub(0);
			}
			break;
		}
		System.out.println("Unwritten LocSet: "+locSet);

		Set<Term> arr = getInnerLocSets();
		Set<Term> ret = new HashSet<>();
		Term retTerm = null;
		if(locSet!=null){
			for(Term a:arr){
				if(locSet.sub(0)==a.sub(0)) {//Same array
					ret.add(tb.sub(a, locSet));
				}
			}
		}
		retTerm = tb.union(ret);
		System.out.println("Written LocSets is: "+retTerm);

		return retTerm;
	}

	private Statement reconstructOuterLoop(Sequent seq) {
		Statement newOuterLoop =null;
		for (final SequentFormula sf : seq.succedent()) {
			if (sf.formula().op() == Modality.DIA) {
				ProgramElement pe = sf.formula().javaBlock().program();
				Statement activePE;
				if (pe instanceof ProgramPrefix) {
					activePE = (Statement) ((ProgramPrefix) pe).getLastPrefixElement().getFirstElement();
				} else {
					activePE = (Statement) pe.getFirstElement();
				}
				if (activePE instanceof While) {
					Expression outerLoopGuard = ((While) activePE).getGuardExpression();
					Expression lastExpression = null;
					Statement outerLoopBody = ((While) activePE).getBody();
					if(outerLoopBody.getFirstElement() instanceof While){
						System.out.println(outerLoopBody.getFirstElement());
						System.out.println("Inner loop is here and should be removed");
						lastExpression = (Expression) outerLoopBody.getLastElement();
						newOuterLoop = new While(outerLoopGuard, (Statement) lastExpression);
						System.out.println("New Outer Loop: " + newOuterLoop);
					}
				}
			}
			break;
		}
		return newOuterLoop;
	}


	private LoopInvariantGenerationResult innerLIComputation(Goal g, int itrNumber, Statement activePE) {
		System.out.println("Entered innerLIComputation");
		Sequent oldSeq = g.sequent();

		StatementBlock stmtBlck = new StatementBlock(activePE);
		JavaBlock jb = JavaBlock.createJavaBlock(stmtBlck);
		Term newDiamond = tb.dia(jb, tb.tt());
		SequentFormula newSF = new SequentFormula(newDiamond);
		Semisequent newSucc = new Semisequent(newSF);

		SemisequentChangeInfo ssci = new SemisequentChangeInfo();
		ssci.removedFormula(0,g.sequent().succedent().getFirst());
		ssci.addedFormula(0,newSF);
		SequentChangeInfo sci = SequentChangeInfo.createSequentChangeInfo(false,ssci, Sequent.createSequent(g.sequent().antecedent(), newSucc),oldSeq);
		g.setSequent(sci);
		System.out.println("new goal seq: "+ g.sequent());

		List<Goal> gList = new ArrayList<>(Arrays.asList(g));
		ImmutableList<Goal> gImList = ImmutableList.fromList(gList);

		do{
			System.out.println("Inner Iteration Number: " + itrNumber);
			oldInnerDepPreds.clear();
			oldInnerCompPreds.clear();

			oldInnerDepPreds.addAll(innerDepPreds);
			oldInnerCompPreds.addAll(innerCompPreds);

			ImmutableList<Goal> goalsAfterUnwind = ruleApp.applyUnwindRule(gImList);
			gImList = ruleApp.applyShiftUpdateRule(goalsAfterUnwind);
			Goal currGoal = ruleApp.findLoopUnwindTacletGoal(gImList);

			PredicateRefiner prInner = new LoopIndexAndDependencyPredicateRefiner(currGoal.sequent(), innerDepPreds, innerCompPreds, indexInner, itrNumber, services);
			itrNumber++;
			Pair<Set<Term>, Set<Term>> refinedPredsInner = prInner.refine();
			innerDepPreds = refinedPredsInner.first;
			innerCompPreds = refinedPredsInner.second;
			for (Goal gl : gImList) {
				if(gl!=null)
					abstractGoal(gl, innerCompPreds, innerDepPreds);
			}
		} while ((!innerCompPreds.equals(oldInnerCompPreds) || !innerDepPreds.equals(oldInnerDepPreds)) || itrNumber < 2);

		innerCompPreds.addAll(innerDepPreds);
		PredicateSetCompressor psc = new PredicateSetCompressor(innerCompPreds,g.sequent(),false,services);
		innerCompPreds = psc.compress();

		System.out.println("Inner Loop Invariant Is:::::::::::::::::::::::::::");
		for(Term t: innerCompPreds){
			System.out.println(t);
		}
		LoopInvariantGenerationResult loopInvariantGenerationResult = new LoopInvariantGenerationResult(innerCompPreds, itrNumber);
		return loopInvariantGenerationResult;

	}
}
