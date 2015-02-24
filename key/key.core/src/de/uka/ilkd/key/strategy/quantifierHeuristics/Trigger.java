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

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;

public interface Trigger {
    
    /**
     * @param targetTerm
     * @param services
     * @return all substitution that found from the targeTerm by matching 
     * this trigger to targeTerm.
     */
    public abstract ImmutableSet<Substitution> 
                           getSubstitutionsFromTerms(ImmutableSet<Term> targetTerm, 
                                   TermServices services);
    
    public abstract Term getTriggerTerm();
}