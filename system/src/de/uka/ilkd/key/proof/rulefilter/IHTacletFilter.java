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

import java.util.HashMap;
import java.util.LinkedHashMap;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;

/**
 * Filter that selects taclets using the method <code>admissible</code> of the
 * <code>Taclet</code> class, i.e. with respect to active heuristics and the
 * <code>interactive</code> flag.
 * If the interactive flag is
 * set the following procedure is used: the non-interactive marked
 * rules are only taken if the given list of heuristics contains at
 * least one heuristic of that rule. If the interactive flag is not
 * set, a rule is taken if the intersection between the given
 * heuristics and the heuristics of the rule is not empty.
 */
public class IHTacletFilter extends TacletFilter {
    private final boolean interactive;
    private final ImmutableList<RuleSet> heuristics;

    
    private final HashMap<Taclet, Boolean> filterCache = new LinkedHashMap<Taclet, Boolean>(2000);
    
    
    
    public IHTacletFilter ( boolean interactive, ImmutableList<RuleSet> heuristics ) {
	this.interactive = interactive;
	this.heuristics  = heuristics;
    }

    /**
     * @return true iff <code>taclet</code> should be included in the
     * result
     */
    public boolean filter ( Taclet taclet ) {
	if (!interactive) {
	    Boolean b = filterCache.get(taclet);
            if (b == null) {
                b = taclet.admissible ( interactive, heuristics ) ? 
                        Boolean.TRUE : Boolean.FALSE; 
                filterCache.put(taclet, b);
            } 
            return b.equals(Boolean.TRUE);
        }
        // in interactive case we do not need to cache; the user is too slow ;-)
        return taclet.admissible ( interactive, heuristics );
    }
}
