package de.uka.ilkd.key.loopinvgen;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.prover.impl.ApplyStrategyInfo;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.IDefaultStrategyPropertiesFactory;
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;
import de.uka.ilkd.key.util.Triple;
import org.key_project.util.LRUCache;

public class SideProof {

	private final Services services;
	private final TermBuilder tb;
	private final Sequent seq;
	private final int maxRuleApp;

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
	static LRUCache<CacheKey, CacheValue> cache = new LRUCache<>(200);

	public SideProof(Services s, Sequent sequent, int maxRuleApp) {
		services = s;
		tb = services.getTermBuilder();
		seq = sequent;
		this.maxRuleApp = maxRuleApp;
	}

	public SideProof(Services s, Sequent sequent) {
		this(s, sequent, 100000);
	}

	boolean proofEquality(Term loc1, Term loc2) {
//		System.out.println("proofEquality");
		Term fml = tb.equals(loc1, loc2);
		Sequent sideSeq = prepareSideProof(loc1, loc2);
		sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();

		boolean closed = isProvable(sideSeq, services);
		// true: Holds, false: Unknown
//		if (closed) {
//			System.out.println("Equlity: "+sideSeq);
//			System.out.println(loc1 + " is NOT equal to " + loc2 + " in: \n" + ProofSaver.printAnything(sideSeq, services));
//			System.out.println("the original seq: "+ seq);
//		}
		return closed;
	}

	boolean proofSubSet(Term loc1, Term loc2) {
//		System.out.println("proofSubSet");
		Term fml = tb.subset(loc1, loc2);
		Sequent sideSeq = prepareSideProof(loc1, loc2);
		sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();

		boolean closed = isProvable(sideSeq, services);
		// true: Holds, false: Unknown
//		if (!closed) {
//			System.out.println("========================\n"+ProofSaver.printAnything(sideSeq, services));		
//			System.out.println(loc1 + " is NOT subset of " + loc2);
//		}
		return closed;
	}

	boolean proofLT(Term ts1, Term ts2) {
//		System.out.println("proofLT");
		Term fml = tb.lt(ts1, ts2);
		Sequent sideSeq = prepareSideProof(ts1, ts2);
		sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();
//		sideSeq = sideSeq.addFormula(cIndexFormula, true, true).sequent();

		boolean closed = isProvable(sideSeq, services);
//		if (closed) {
//			System.out.println("Less than: " + sideSeq);
//			System.out.println(
//					ts1 + " is NOT less than " + ts2 + " in: \n" + ProofSaver.printAnything(sideSeq, services));
//			System.out.println("the original seq: " + seq);
//		}
		return closed;
	}

	/**
	 * initializes the sequent for the side proof depending on the terms t1 and ts2
	 * @param ts1 Term used to initialize the sequent
	 * @param ts2 Term used to initialize the sequent
	 * @return the initialized sequent
	 */
	private Sequent prepareSideProof(Term ts1, Term ts2) {
		final CacheKey key = new CacheKey(ts1, ts2);
		CacheValue value= cache.get(key);

		Sequent sideSeq;
		if (value != null) {
			value.hitCount++;
			sideSeq = value.seq;
			if (value.hitCount == 2) {
				// if the seq is request at least twice we perform some simplifications to
				// avoid repetitions
				try {
					ApplyStrategyInfo info = isProvableHelper(sideSeq, 1000, true, services);
					if (info.getProof().openGoals().size() != 1) {
						throw new ProofInputException("simplification of sequent failed. Open goals " + info.getProof().openGoals().size());
					}
					sideSeq = info.getProof().openGoals().head().sequent();
				} catch (ProofInputException e) {
					e.printStackTrace();
				}
				value.seq = sideSeq;
			}

			return sideSeq;
		}
		sideSeq = Sequent.EMPTY_SEQUENT;
		Set<Term> locSetVars = new HashSet<>();

		if (ts1.subs().isEmpty()) {
			locSetVars.addAll(collectProgramAndLogicVariables(ts1));
		} else {
			for (Term t : ts1.subs()) {
				locSetVars.addAll(collectProgramAndLogicVariables(t));
			}
		}
		if (ts2.subs().isEmpty()) {
			locSetVars.addAll(collectProgramAndLogicVariables(ts2));
		} else {
			for (Term t : ts2.subs()) {
				locSetVars.addAll(collectProgramAndLogicVariables(t));
			}
		}

		Set<Term> anteFmlVars;
		Set<SequentFormula> tempAnteToAdd = new HashSet<>();
		Set<SequentFormula> tempSuccToAdd = new HashSet<>();
		int size;

		do {
			size = locSetVars.size();
			for (SequentFormula sfAnte : seq.antecedent()) {
				anteFmlVars = collectProgramAndLogicVariables(sfAnte.formula());
				for (Term tfv : anteFmlVars) {
					if (locSetVars.contains(tfv)) {
						if (tempAnteToAdd.add(sfAnte)) {
							sideSeq = sideSeq.addFormula(sfAnte, true, true).sequent();
							locSetVars.addAll(anteFmlVars);
							break;
						}
					}
				}
			}

			Set<Term> succFmlVars;
			for (SequentFormula sfSucc : seq.succedent()) {
				succFmlVars = collectProgramAndLogicVariables(sfSucc.formula());
				for (Term tfv : succFmlVars) {
					if (locSetVars.contains(tfv)) {
						if (tempSuccToAdd.add(sfSucc)) {
							sideSeq = sideSeq.addFormula(sfSucc, false, true).sequent();
							locSetVars.addAll(succFmlVars);
							break;
						}
					}
				}
			}
		} while (size != locSetVars.size());

		cache.put(key, new CacheValue(sideSeq));
		return sideSeq;
	}

	boolean proofLEQ(Term ts1, Term ts2) {
//		System.out.println("proofLEQ");
		Term fml = tb.leq(ts1, ts2);
//		sideSeq = sideSeq.addFormula(cIndexFormula, true, true).sequent();

		Sequent sideSeq = prepareSideProof(ts1, ts2);
		sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();

		boolean closed = isProvable(sideSeq, maxRuleApp, services);
//		if (closed) {
//			System.out.println("Less than: " + sideSeq);
//			System.out.println(
//					ts1 + " is NOT less than " + ts2 + " in: \n" + ProofSaver.printAnything(sideSeq, services));
//			System.out.println("the original seq: " + seq);
//		}
		return closed;
	}

	
	boolean proofNonEmptyIntersection(Term ts1, Term ts2) {
//		System.err.println("proofNonEmptyIntersection");
		Term fml = tb.not(tb.equals(tb.intersect(ts1, ts2), tb.empty()));
		Sequent sideSeq = prepareSideProof(ts1, ts2);
		sideSeq = sideSeq.addFormula(new SequentFormula(fml), false, true).sequent();

		return isProvable(sideSeq, maxRuleApp, services);
	}

	public static ApplyStrategyInfo isProvableHelper(Sequent seq2prove, int maxRuleApp, boolean simplifyOnly, Services services) throws ProofInputException {
		//		System.out.println("isProvable: " + seq2prove);

		final ProofStarter ps = new ProofStarter(false);

		final ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());

		ps.init(seq2prove, env, "IsInRange Proof");

		StrategyProperties sp = null;
		
		if (simplifyOnly) {
			var defaults =
					ps.getProof().getActiveStrategyFactory().getSettingsDefinition().getFurtherDefaults();
			//Simplification
			for (var el : defaults) {
				if (el.first.equals("Simplification")) {
					sp = el.third.createDefaultStrategyProperties();
					ps.setStrategy(new DepSimplificationStrategy(ps.getProof(), sp));
					break;
				}
			}
		}

		if (sp == null) {
			sp = ps.getProof().getActiveStrategyFactory().getSettingsDefinition()
					.getDefaultPropertiesFactory().createDefaultStrategyProperties();
		}

//		System.out.println("strategy prop. " + sp);

		ps.setStrategyProperties(sp);

		ps.getProof().getSettings().getStrategySettings().setActiveStrategyProperties(sp);

		ps.setMaxRuleApplications(maxRuleApp);
		ps.setTimeout(-1);
		return ps.start();
	}

	protected boolean isProvable(Sequent seq2prove, Services services) {
		return isProvable(seq2prove, maxRuleApp, services);
	}

	public static boolean isProvable(Sequent seq2prove, int maxRuleApp, Services services) {
		ApplyStrategyInfo info;
		try {
			info = isProvableHelper(seq2prove, maxRuleApp, false, services);
		} catch (ProofInputException pie) {
			pie.printStackTrace();
			return false;
		}
//		System.out.println(info.getAppliedRuleApps() + ":" + info.toString());


//		System.out.println("rules: "+ ps.getProof().getStatistics());
//		if (!info.getProof().closed()) {
//			System.out.println("Open Goals: " + info.getProof().openGoals());
//		}
//System.out.println("==>" + info.getAppliedRuleApps());

		boolean closed = info.getProof().closed();

//		if(!closed) {
//			System.out.println(info.reason() + " CO" + COUNTER);
//			System.out.println(" proof could not be closed for " + ps.getProof());
//			System.out.println(" proof could not be closed for " + seq2prove.succedent());
//		**		
		try {
				new ProofSaver(info.getProof(), new java.io.File("C:\\Users\\Asma\\testNoRMissing"+COUNTER+".key")).save();
				System.out.println(COUNTER);
			} catch (IOException e) {
//				 TODO Auto-generated catch block
				e.printStackTrace();
			}
			COUNTER++;
//		}
		System.out.println(closed);
		return closed;
	}

static long COUNTER=0;
//	Term expr2term(Expression expr) {
//		return this.services.getTypeConverter().convertToLogicElement(expr);
//	}

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

//	public void setMaxStep(int i) {
//		maxRuleApp = i;
//	}
}
