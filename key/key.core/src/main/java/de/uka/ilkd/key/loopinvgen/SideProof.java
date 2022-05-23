package de.uka.ilkd.key.loopinvgen;

import java.io.IOException;
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
import de.uka.ilkd.key.util.ProofStarter;
import de.uka.ilkd.key.util.SideProofUtil;

public class SideProof {

	private final Services services;
	private final TermBuilder tb;
	private final Sequent seq;
	private int maxRuleApp;

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
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		if (loc1.subs().isEmpty()) {
			locSetVars.addAll(collectProgramAndLogicVariables(loc1));
		} else {
			for (Term t : loc1.subs()) {
				locSetVars.addAll(collectProgramAndLogicVariables(t));
			}
		}
		if (loc2.subs().isEmpty()) {
			locSetVars.addAll(collectProgramAndLogicVariables(loc2));
		} else {
			for (Term t : loc2.subs()) {
				locSetVars.addAll(collectProgramAndLogicVariables(t));
			}
		}

		Set<Term> anteFmlVars = new HashSet<Term>();
		Set<SequentFormula> tempAnteToAdd = new HashSet<SequentFormula>();
		Set<SequentFormula> tempSuccToAdd = new HashSet<SequentFormula>();
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

			Set<Term> succFmlVars = new HashSet<Term>();
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
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();
		if (loc1.subs().isEmpty()) {
			locSetVars.addAll(collectProgramAndLogicVariables(loc1));
		} else {
			for (Term t : loc1.subs()) {
				locSetVars.addAll(collectProgramAndLogicVariables(t));
			}
		}
		if (loc2.subs().isEmpty()) {
			locSetVars.addAll(collectProgramAndLogicVariables(loc2));
		} else {
			for (Term t : loc2.subs()) {
				locSetVars.addAll(collectProgramAndLogicVariables(t));
			}
		}

		Set<Term> anteFmlVars = new HashSet<Term>();
		Set<SequentFormula> tempAnteToAdd = new HashSet<SequentFormula>();
		Set<SequentFormula> tempSuccToAdd = new HashSet<SequentFormula>();
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

			Set<Term> succFmlVars = new HashSet<Term>();
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
		boolean closed = isProvable(sideSeq, services);
		// true: Holds, false: Unknown
		if (!closed) {
//			System.out.println("========================\n"+ProofSaver.printAnything(sideSeq, services));		
//			System.out.println(loc1 + " is NOT subset of " + loc2);
		}
		return closed;
	}

	boolean proofLT(Term ts1, Term ts2) {
//		System.out.println("proofLT");
		Term fml = tb.lt(ts1, ts2);
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
//		sideSeq = sideSeq.addFormula(cIndexFormula, true, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();

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

		Set<Term> anteFmlVars = new HashSet<Term>();
		Set<SequentFormula> tempAnteToAdd = new HashSet<SequentFormula>();
		Set<SequentFormula> tempSuccToAdd = new HashSet<SequentFormula>();
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

			Set<Term> succFmlVars = new HashSet<Term>();
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

		boolean closed = isProvable(sideSeq, services);
//		if (closed) {
//			System.out.println("Less than: " + sideSeq);
//			System.out.println(
//					ts1 + " is NOT less than " + ts2 + " in: \n" + ProofSaver.printAnything(sideSeq, services));
//			System.out.println("the original seq: " + seq);
//		}
		return closed;
	}

	boolean proofLEQ(Term ts1, Term ts2) {
//		System.out.println("proofLEQ");
		Term fml = tb.leq(ts1, ts2);
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml), false, true).sequent();
//		sideSeq = sideSeq.addFormula(cIndexFormula, true, true).sequent();

		Set<Term> locSetVars = new HashSet<Term>();

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

		Set<Term> anteFmlVars = new HashSet<Term>();
		Set<SequentFormula> tempAnteToAdd = new HashSet<SequentFormula>();
		Set<SequentFormula> tempSuccToAdd = new HashSet<SequentFormula>();
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

			Set<Term> succFmlVars = new HashSet<Term>();
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

		boolean closed = isProvable(sideSeq, services);
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
		Term fml_1 = tb.not(tb.equals(tb.intersect(ts1, ts2), tb.empty()));
		Set<Term> locSetVars = new HashSet<Term>();
		Sequent sideSeq = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(fml_1), false, true).sequent();

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

		Set<Term> anteFmlVars = new HashSet<Term>();
		Set<SequentFormula> tempAnteToAdd = new HashSet<SequentFormula>();
		Set<SequentFormula> tempSuccToAdd = new HashSet<SequentFormula>();
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

			Set<Term> succFmlVars = new HashSet<Term>();
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

		boolean closed = isProvable(sideSeq, services);
		return closed;
	}

	protected boolean isProvable(Sequent seq2prove, Services services) {
		final ProofStarter ps = new ProofStarter(false);
//		System.out.println("isProvable: " + seq2prove);
		
		Term antec = tb.tt();
		for (SequentFormula sf : seq2prove.antecedent()) {
			antec = tb.and(antec, sf.formula());
		}
		
		Term succ = tb.ff();
		for (SequentFormula sf : seq2prove.succedent()) {
			succ = tb.or(succ, sf.formula());
		}
		
		seq2prove = Sequent.EMPTY_SEQUENT.addFormula(new SequentFormula(tb.imp(antec, succ)), false, true).sequent();
		
		final ProofEnvironment env = SideProofUtil.cloneProofEnvironmentWithOwnOneStepSimplifier(services.getProof());

		try {
			ps.init(seq2prove, env, "IsInRange Proof");
		} catch (ProofInputException pie) {
			pie.printStackTrace();
			return false;
		}

		final StrategyProperties sp = ps.getProof().getActiveStrategyFactory().getSettingsDefinition()
				.getDefaultPropertiesFactory().createDefaultStrategyProperties();
		
		ps.setStrategyProperties(sp);
		
		ps.getProof().getSettings().getStrategySettings().setActiveStrategyProperties(sp);
		
		ps.setMaxRuleApplications(maxRuleApp);
		ps.setTimeout(-1);
//		System.out.println("strategy prop. " + sp);

		
		
		final ApplyStrategyInfo info = ps.start();
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
				new ProofSaver(ps.getProof(), new java.io.File("C:\\Users\\Asma\\testNoRMissing"+COUNTER+".key")).save();
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
		Set<Term> res = new HashSet<Term>();
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
