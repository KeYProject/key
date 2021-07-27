// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

public interface Trigger {
    
    /**
     * @param targetTerm
     * @param services
     * @return all substitution that found from the targeTerm by matching 
     * this trigger to targeTerm.
     */
    public abstract ImmutableSet<Substitution> 
                           getSubstitutionsFromTerms(ImmutableSet<Term> targetTerm, 
                                   Services services);
    
    public abstract Term getTriggerTerm();
}