package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import org.key_project.util.LRUCache;
import org.key_project.util.collection.ImmutableList;

import java.io.IOException;
import java.util.HashSet;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Provides means to perform side proofs required by the loop invariant generator.
 * Such a side proof is need for instance to check whether a set of formulas implies
 * that for the values of two arithmetic terms t1 and t2 the ordering t1 < t2 holds.
 */
public class SideProof {

	//0: off, 1: save proof files and print short proof info, 2: verbose output
	private static final int DEBUG_VERBOSITY = 1;

	static LRUCache<CacheKey, CacheValue> cache = new LRUCache<>(200);
	private final Services services;
	private final TermBuilder tb;
	private final Sequent seq;
	private final int maxRuleApp;

	public SideProof(Services s, Sequent sequent, int maxRuleApp) {
		services = s;
		tb = services.getTermBuilder();
		seq = sequent;
		this.maxRuleApp = maxRuleApp;
	}

	public SideProof(Services s, Sequent sequent) {
		this(s, sequent, 20000);
	}//100000

	/**
	 * simplifies the given sequent
	 * @param sequent the Sequent to simplify
	 * @return the simplified sequent
	 */
	public static Sequent simplifySequent(Sequent sequent, Services services) {
		try {
			ApplyStrategyInfo info = isProvableHelper(sequent, 1000,
					true, false, services);
			if (info.getProof().openGoals().size() != 1) {
				throw new ProofInputException("simplification of sequent failed. Open goals " + info.getProof().openGoals().size());
			}
			sequent = info.getProof().openGoals().head().sequent();
		} catch (ProofInputException e) {
			e.printStackTrace();
		}
		return sequent;
	}

	public static ApplyStrategyInfo isProvableHelper(Sequent seq2prove,
													 int maxRuleApp, boolean simplifyOnly,
													 boolean stopAtFirstUncloseableGoal,
													 Services services) throws ProofInputException {
		final ProofStarter ps = new ProofStarter(false);
		final ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());
		ps.init(seq2prove, env, "IsInRange Proof");

		StrategyProperties sp = null;
		final StrategySettingsDefinition strategyDefinition = ps.getProof().getActiveStrategyFactory().getSettingsDefinition();

		if (simplifyOnly) {
			//Simplification
			for (var el : strategyDefinition.getFurtherDefaults()) {
				if (el.first.equals("Simplification")) {
					sp = el.third.createDefaultStrategyProperties();
					ps.setStrategy(new DepSimplificationStrategy(ps.getProof(), sp));
					break;
				}
			}
		}
		if (sp == null) {
			sp = strategyDefinition.getDefaultPropertiesFactory().createDefaultStrategyProperties();
		}

		sp.setProperty(StrategyProperties.OSS_OPTIONS_KEY, StrategyProperties.OSS_OFF);

		if (stopAtFirstUncloseableGoal) {
			sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_NONCLOSE);
		} else {
			sp.setProperty(StrategyProperties.STOPMODE_OPTIONS_KEY, StrategyProperties.STOPMODE_DEFAULT);
		}

		if (simplifyOnly) {
			sp.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY, StrategyProperties.SPLITTING_OFF);
		}

		ps.setStrategyProperties(sp);
		ps.getProof().getSettings().getStrategySettings().setActiveStrategyProperties(sp);
		ps.setMaxRuleApplications(maxRuleApp);
		ps.setTimeout(-1);

//		try {
//			new ProofSaver(ps.getProof(), new java.io.File("C:\\Users\\Asma\\AAAAA.key")).save();
//		} catch (IOException e) {
//			e.printStackTrace();
//		}

		return ps.start();
	}

		static long COUNTER=0; // only used for saving - unique filenames
	private static void printDebugAndSaveProof(ApplyStrategyInfo info) {
		if (DEBUG_VERBOSITY == 0) return;
//		System.out.println("Proof Status: " + (info.getProof().closed() ? "closed" : "open"));

		if (DEBUG_VERBOSITY > 1) {
//			System.out.println(info.getAppliedRuleApps() + ":" + info.toString());
//			System.out.println("Rules: " + info.getProof().getStatistics());
//			if (!info.getProof().closed()) {
//				System.out.println("Open Goals: " + info.getProof().openGoals());
//			}
//			System.out.println("Applied rules:" + info.getAppliedRuleApps());
		}


		try {
			new ProofSaver(info.getProof(), new java.io.File("C:\\Users\\Asma\\Unprovable"+COUNTER+".key")).save();
			System.out.println(COUNTER + "   " +info.getProof().closed());
		} catch (IOException e) {
			e.printStackTrace();
		}
		COUNTER++;
	}

	public static boolean isProvable(Sequent seq2prove, int maxRuleApp,
									 boolean stopAtFirstUncloseableGoal,
									 Services services) {
		ApplyStrategyInfo info;
		try {
			info = isProvableHelper(seq2prove, maxRuleApp, false, stopAtFirstUncloseableGoal, services);

//			if (!info.getProof().closed() && info.getProof().openGoals().size() == 1) {
//				System.out.println(LogicPrinter.quickPrintSequent(info.getProof().openGoals().head().sequent(), services));
//
//			}

		} catch (ProofInputException pie) {
			pie.printStackTrace();
			return false;
		}

		boolean closed = info.getProof().closed();

		if (DEBUG_VERBOSITY > 0) printDebugAndSaveProof(info);

		return closed;
	}

	public boolean proofEquality(Term left, Term right) {
		if(left!=null && right!=null){
			Term fml = tb.equals(left, right);
			Sequent sideSeq = prepareSideProof(left, right, sf->services.getTypeConverter().getDependenciesLDT().isDependencePredicate(sf.formula().op()));
			sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();
			boolean closed = isProvable(sideSeq, services);
			// true: Holds, false: Unknown
			return closed;
		}
		return false;
	}

	public boolean proofNonEmptyIntersection(Term left, Term right) {
		Term fml = tb.not(tb.equals(tb.intersect(left, right), tb.empty()));
		Sequent sideSeq = prepareSideProof(left, right, sf->services.getTypeConverter().getDependenciesLDT().isDependencePredicate(sf.formula().op()));
		sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();
		boolean closed = isProvable(sideSeq, maxRuleApp, true, services);
		// true: Holds, false: Unknown
		return closed;
	}

	public boolean proofSubSet(Term left, Term right) {
		Function pred = services.getTypeConverter().getLocSetLDT().getSubset();
		return prove(pred, left, right);
	}

	public boolean proofLT(Term left, Term right) {
		Function pred = services.getTypeConverter().getIntegerLDT().getLessThan();
		return prove(pred, left, right);
	}

	public boolean proofLEQ(Term left, Term right) {
		Function pred = services.getTypeConverter().getIntegerLDT().getLessOrEquals();
		return prove(pred, left, right);
	}

	public ImmutableList<Goal> retGoal(){
		return this.services.getProof().openGoals();
	}
	private boolean prove(Function pred, Term ts1, Term ts2) {
		Term fml = tb.func(pred, ts1, ts2);
		Sequent sideSeq = prepareSideProof(ts1, ts2,
				sf-> services.getTypeConverter().getDependenciesLDT().isDependencePredicate(sf.formula().op()));
		sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();
		// true: Holds, false: Unknown
		return isProvable(sideSeq, services);
	}

	/**
	 * initializes the sequent for the side proof depending on the terms t1 and ts2
	 * @param ts1 Term used to initialize the sequent
	 * @param ts2 Term used to initialize the sequent
	 * @return the initialized sequent
	 */
	private Sequent prepareSideProof(Term ts1, Term ts2, Predicate<SequentFormula> filter) {
		final CacheKey key = new CacheKey(ts1, ts2);
		CacheValue value= cache.get(key);
		if (value != null) {
			value.hitCount++;
			if (value.hitCount == 2) {
				// if the seq is request at least twice we perform some simplifications to
				// avoid repetitions
				value.seq = simplifySequent(value.seq, services);
			}
			return value.seq;
		}

		Sequent sideSeq = Sequent.EMPTY_SEQUENT;

		Set<Term> locSetVars = new HashSet<>();
		locSetVars.addAll(collectProgramAndLogicVariables(ts1));
		locSetVars.addAll(collectProgramAndLogicVariables(ts2));

		final Set<SequentFormula> tempAnteToAdd = new HashSet<>();
		final Set<SequentFormula> tempSuccToAdd = new HashSet<>();
		int size;
		do {
			size = locSetVars.size();
			sideSeq = addRelevantSequentFormulas(seq.antecedent(), tempAnteToAdd, locSetVars, sideSeq, true, filter);
			sideSeq = addRelevantSequentFormulas(seq.succedent(), tempSuccToAdd, locSetVars, sideSeq, false, filter);
		} while (size != locSetVars.size());

		cache.put(key, new CacheValue(sideSeq));
		return sideSeq;
	}

	/**
	 * determines relevant formulas of the given semisequent to add. Relevant formulas are those that have
	 * program variables or constant symbols common with those in locSetVars
	 * @param seq the Semisequent where to look for relevant formulas
	 * @param tempAnteToAdd Set of newly added formulas to the antecedent
	 * @param locSetVars Set of newly added formulas to the succedent
	 * @param sideSeq the Sequent reflecting the current state of the to be constructed sequent
	 * @param antec boolean indicating whether the given semisequent is the antecedent or succedent of the original sequent
	 * @return the resulting sequent with added relevant formulas to sideSeq
	 */
	private Sequent addRelevantSequentFormulas(Semisequent seq, Set<SequentFormula> tempAnteToAdd,
											   Set<Term> locSetVars, Sequent sideSeq, boolean antec, Predicate<SequentFormula> filter) {
		for (SequentFormula sfAnte : seq) {
			if (tempAnteToAdd.contains(sfAnte) || filter.test(sfAnte)) {
				continue;
			}
			final Set<Term> anteFmlVars = collectProgramAndLogicVariables(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					if (tempAnteToAdd.add(sfAnte)) {
						sideSeq = sideSeq.addFormula(sfAnte, antec, true).sequent();
						locSetVars.addAll(anteFmlVars);
						break;
					}
				}
			}
		}
		return sideSeq;
	}
/*

	private Sequent addRelevantSequentFormulas(Semisequent seq, Set<SequentFormula> tempAnteToAdd,
											   Set<Term> locSetVars, Sequent sideSeq, boolean antec, boolean noDep) {
		DependenciesLDT depLDT = services.getTypeConverter().getDependenciesLDT();

		LinkedList<SequentFormula> queue = new LinkedList<>();
		for (SequentFormula sfAnte : seq) {
			queue.add(sfAnte);
		}
		LinkedList<SequentFormula> newQueue = new LinkedList<>();
		while (!queue.isEmpty()) {
		for (SequentFormula sfAnte = queue.pop(); !queue.isEmpty(); sfAnte = queue.pop()) {
			if (tempAnteToAdd.contains(sfAnte)) {
				continue;
			}
			final Set<Term> anteFmlVars = collectProgramAndLogicVariables(sfAnte.formula());
			for (Term tfv : anteFmlVars) {
				if (locSetVars.contains(tfv)) {
					if (tempAnteToAdd.add(sfAnte) && (!noDep || !depLDT.isDependencePredicate(sfAnte.formula().op()))) {
						sideSeq = sideSeq.addFormula(sfAnte, antec, true).sequent();
						locSetVars.addAll(anteFmlVars);
						break;
					} else {
						newQueue.add(sfAnte);
					}
				}
			}
		}
			queue = newQueue;
		}
		return sideSeq;
	}
 */
	protected boolean isProvable(Sequent seq2prove, Services services) {
//		System.out.println(seq2prove);
		return isProvable(seq2prove, maxRuleApp, true, services);
	}

	private Set<Term> collectProgramAndLogicVariables(Term term) {
		Set<Term> res = new HashSet<>();
		if (!term.containsJavaBlockRecursive()) {
			if (term.op() instanceof ProgramVariable) {
				res.add(term);
			} else if (term.op() instanceof Function && term.sort() != Sort.FORMULA
					&& (term.arity() == 0 || term.arity() == 1) && term.freeVars().isEmpty()) {
				res.add(term);

			} else
				for (Term sub : term.subs())
					res.addAll(collectProgramAndLogicVariables(sub));
		}
		return res;
	}

	// cache
	// the key of the cache is a set, i.e., the order of the terms is not of relevance
	static class CacheKey {
		final Term t1;
		final Term t2;

		public CacheKey(Term t1, Term t2) {
			this.t1 = t1;
			this.t2 = t2;
		}
		@Override
		public boolean equals(Object o) {
			if (this == o) return true;
			if (o == null || getClass() != o.getClass()) return false;
			CacheKey sPair = (CacheKey) o;
			if (!t1.equals(sPair.t1)) {
				if (!t1.equals(sPair.t2)) {
					return false;
				} else {
					return t2.equals(sPair.t1);
				}
			} else {
				return t2.equals(sPair.t2);
			}
		}

		@Override
		public int hashCode() {
			return t1.hashCode() + t2.hashCode();
		}
	}
	static class CacheValue {
		Sequent seq;
		int hitCount;

		public CacheValue(Sequent seq) {
			this.seq = seq;
		}
	}
}

