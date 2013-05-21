// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof.rulefilter;

import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;

/**
 * Interface for filtering a list of TacletApps, for example to 
 * choose only taclets for interactive application or taclets 
 * belonging to some given heuristics.
 */
public abstract class TacletFilter implements RuleFilter {
    /**
     * Trival TacletFilter that always returns true;
     */
    public static final TacletFilter TRUE = new TacletFilterTrue ();
    
    public boolean filter ( Rule rule ) {
        if ( rule instanceof Taclet )
            return filter ( (Taclet) rule );
        return false;
    }

    /**
     * @return true iff <code>taclet</code> should be included in the
     * result
     */
    protected abstract boolean filter ( Taclet taclet );

    /**
     * Trival TacletFilter that always returns true;
     */
    static class TacletFilterTrue extends TacletFilter {
        protected boolean filter ( Taclet taclet ) {
	    return true;
	}
    }
}
