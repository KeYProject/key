// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;

public class RuleAppSMT implements RuleApp {

    private final static SMTRule rule = new SMTRule();
    private String title;

    public RuleAppSMT(Goal goal, String title) {
	this.title = title;
	goal.proof().env().getJustifInfo().addJustification(rule,
	        new RuleJustification() {

		    @Override
		    public boolean isAxiomJustification() {
		        return false;
		    }
	        });
    }

    @Override
    public boolean complete() {
	return true;
    }

    @Override
    public Constraint constraint() {
	return Constraint.BOTTOM;
    }

    @Override
    public ImmutableList<Goal> execute(Goal goal, Services services) {
	goal.addAppliedRuleApp(this);

	goal.split(1);

	goal.proof().closeGoal(goal, Constraint.BOTTOM);
	goal.node().getNodeInfo().setBranchLabel(title);
	return null;
    }

    @Override
    public PosInOccurrence posInOccurrence() {
	return null;
    }

    @Override
    public Rule rule() {

	return rule;
    }

    private static class SMTRule implements BuiltInRule {
	private Name name = new Name("SMTRule");

	@Override
	public boolean isApplicable(Goal goal, PosInOccurrence pio,
	        Constraint userConstraint) {
	    return false;
	}

	@Override
	public ImmutableList<Goal> apply(Goal goal, Services services,
	        RuleApp ruleApp) {
	    return null;
	}

	@Override
	public String displayName() {
	    return "SMT";
	}

	public String toString() {
	    return displayName();
	}

	@Override
	public Name name() {
	    return name;
	}

    }

}
