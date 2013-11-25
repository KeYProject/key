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


package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** 
 * Simple container class containing the information resulting from a
 * Taclet.match-call 
 */
public class MatchConditions {

    public static final MatchConditions EMPTY_MATCHCONDITIONS =
	new MatchConditions ( SVInstantiations.EMPTY_SVINSTANTIATIONS,
			      RenameTable.EMPTY_TABLE);

    private final SVInstantiations instantiations;
    private final RenameTable renameTable;

    public MatchConditions() {
        this.instantiations = SVInstantiations.EMPTY_SVINSTANTIATIONS;
        this.renameTable = RenameTable.EMPTY_TABLE;
    }
    
    public MatchConditions ( SVInstantiations   p_instantiations,
			     RenameTable        p_renameTable) {
        assert p_instantiations != null;
        assert p_renameTable != null;
	instantiations   = p_instantiations;	
        renameTable      = p_renameTable; 
    }

    public SVInstantiations   getInstantiations   () {
	return instantiations;
    }

    public MatchConditions    setInstantiations   ( SVInstantiations   p_instantiations ) {
	if ( instantiations == p_instantiations )
	    return this;
	else
	    return new MatchConditions ( p_instantiations, 
                                         renameTable );
    }
    
    public MatchConditions extendRenameTable() {        
        return new MatchConditions(instantiations, renameTable.extend());
    }    

    public MatchConditions addRenaming(QuantifiableVariable q1, QuantifiableVariable q2) {        
        return new MatchConditions(instantiations, renameTable.assign(q1, q2));
    }    
    
    public RenameTable renameTable() {
        return renameTable;
    }

    public MatchConditions shrinkRenameTable() {      
        return new MatchConditions(instantiations, renameTable.parent());
    }

    
}
