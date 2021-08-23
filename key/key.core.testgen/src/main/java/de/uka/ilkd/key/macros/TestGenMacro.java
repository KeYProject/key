package de.uka.ilkd.key.macros;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.TestGenerationSettings;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.Strategy;

public class TestGenMacro extends StrategyProofMacro {
	@Override
	protected Strategy createStrategy(Proof proof,
	        PosInOccurrence posInOcc) {
		return new TestGenStrategy(proof
		        .getActiveStrategy());
	}

	@Override
	public String getDescription() {
		return "Finish symbolic execution but restrict loop unwinding.";
	}

	@Override
	public String getName() {
		return "TestGen (finite loop unwinding)";
	}

	@Override
	public String getCategory() {
	    return null;
	}


}

/**
 * The Class FilterAppManager is a special strategy assigning to any rule
 * infinite costs if the goal has no modality
 */
class TestGenStrategy extends FilterStrategy {
	private static final Name NAME = new Name(
			TestGenStrategy.class.getSimpleName());
	private static final Set<String> unwindRules;
	private static final int UNWIND_COST = 1000;
	private final int limit;
	static {
		unwindRules = new HashSet<>();
		TestGenStrategy.unwindRules.add("loopUnwind");
		TestGenStrategy.unwindRules.add("doWhileUnwind");
		TestGenStrategy.unwindRules.add("methodCall");
		TestGenStrategy.unwindRules.add("methodCallWithAssignment");
		TestGenStrategy.unwindRules.add("staticMethodCall");
		TestGenStrategy.unwindRules.add("staticMethodCallWithAssignment");
	}

	/*
	 * recursively descent into the term to detect a modality.
	 */
	private static boolean hasModality(Term term) {
		if (term.op() instanceof Modality) {
			return true;
		}
		for (final Term sub : term.subs()) {
			if (hasModality(sub)) {
				return true;
			}
		}
		return false;
	}


	/*
	 * find a modality term in a node
	 */
	private static boolean hasModality(Node node) {
		final Sequent sequent = node.sequent();
		for (final SequentFormula sequentFormula : sequent) {
			if (hasModality(sequentFormula.formula())) {
				return true;
			}
		}
		return false;
	}


	private static boolean isUnwindRule(Rule rule) {
		if (rule == null) {
			return false;
		}
		final String name = rule.name().toString();
		return TestGenStrategy.unwindRules.contains(name);
	}

	public TestGenStrategy(Strategy delegate) {
		super(delegate);
		limit = TestGenerationSettings.getInstance().getMaximalUnwinds();
	}

	@Override
	public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio,
								   Goal goal) {
		if (TestGenStrategy.isUnwindRule(app.rule())) {
			return NumberRuleAppCost.create(TestGenStrategy.UNWIND_COST);
		}
		return super.computeCost(app, pio, goal);
	}

	private int computeUnwindRules(Goal goal) {
		int totalUnwinds = 0;
		Node node = goal.node();
		while (!node.root()) {
			final RuleApp app = node.getAppliedRuleApp();
			if (app != null) {
				final Rule rule = app.rule();
				if (TestGenStrategy.isUnwindRule(rule)) {
					++totalUnwinds;
				}
			}
			node = node.parent();
		}
		return totalUnwinds;
	}

	@Override
	public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
		if (!hasModality(goal.node())) {
			return false;
		}
		if (TestGenStrategy.isUnwindRule(app.rule())) {
			final int noUnwindRules = computeUnwindRules(goal);
			return noUnwindRules < limit;
		}
		return super.isApprovedApp(app, pio, goal);
	}

	@Override
	public Name name() {
		return TestGenStrategy.NAME;
	}

	@Override
	public boolean isStopAtFirstNonCloseableGoal() {
		return false;
	}
}
