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
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;

public class RuleAppSMT extends BuiltInRuleApp{ //implements RuleApp {

    public final static SMTRule rule = new SMTRule();
    private final String title;


    RuleAppSMT( SMTRule rule, PosInOccurrence pio ) {
    	super(rule, null);
    	title = "SMT Rule App";
    }
    
    private RuleAppSMT(SMTRule rule, String title) {
    	super(rule, null);
    	this.title = title;
    }
    
	public RuleApp replacePos(PosInOccurrence newPos) {
	    return this;
    }

    @Override
    public boolean complete() {
	return true;
    }

    public String getTitle() {
		return title;
	}

    @Override
    public PosInOccurrence posInOccurrence() {
	return null;
    }

    @Override
    public BuiltInRule rule() {

	return rule;
    }

    public static class SMTRule implements BuiltInRule {
	private Name name = new Name("SMTRule");

	public BuiltInRuleApp createApp( PosInOccurrence pos ) {
		return new RuleAppSMT( this, pos );
	}

	
	@Override
	public boolean isApplicable(Goal goal, PosInOccurrence pio) {
	    return false;
	}

	@Override
	public ImmutableList<Goal> apply(Goal goal, Services services,
	        RuleApp ruleApp) {
		if (goal.proof().env().getJustifInfo().getJustification(rule) == null) {
			goal.proof().env().getJustifInfo().addJustification(rule,
					new RuleJustification() {

				@Override
				public boolean isAxiomJustification() {
					return false;
				}
			});
		}

		goal.split(1);	
		RuleAppSMT app = (RuleAppSMT) ruleApp;
		goal.setBranchLabel(app.getTitle());
	    return ImmutableSLList.<Goal>nil();
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

	public BuiltInRuleApp setTitle(String title2) {
	    return null;
    }

}
