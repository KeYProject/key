// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/** 
 * Simple container class containing the information resulting from a
 * Taclet.match-call 
 */
public class MatchConditions {

    public static final MatchConditions EMPTY_MATCHCONDITIONS =
	new MatchConditions ( SVInstantiations.EMPTY_SVINSTANTIATIONS,
			      Constraint.BOTTOM,
			      DefaultImmutableSet.<Metavariable>nil(),
                              RenameTable.EMPTY_TABLE);

    private SVInstantiations   instantiations   = SVInstantiations.EMPTY_SVINSTANTIATIONS;
    private Constraint         constraint       = Constraint.BOTTOM;
    private ImmutableSet<Metavariable>  newMetavariables = DefaultImmutableSet.<Metavariable>nil();

    private RenameTable renameTable = RenameTable.EMPTY_TABLE;

    
    public MatchConditions ( SVInstantiations   p_instantiations,
			     Constraint         p_constraint,
			     ImmutableSet<Metavariable>  p_newMetavariables,
                             RenameTable        p_renameTable) {
	instantiations   = p_instantiations;
	constraint       = p_constraint;
	newMetavariables = p_newMetavariables;
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
                                         constraint, newMetavariables, renameTable );
    }

    public Constraint         getConstraint       () {
	return constraint;
    }

    public MatchConditions    setConstraint       ( Constraint         p_constraint ) {
	if ( constraint == p_constraint )
	    return this;
	else
	    return new MatchConditions ( instantiations, p_constraint, newMetavariables, 
                                         renameTable );
    }

    public ImmutableSet<Metavariable> getNewMetavariables () {
	return newMetavariables;
    }

    public MatchConditions    setNewMetavariables ( ImmutableSet<Metavariable>  p_newMetavariables ) {
	if ( newMetavariables == p_newMetavariables )
	    return this;
	else
	    return new MatchConditions ( instantiations, constraint, p_newMetavariables, renameTable );
    }

    
    public MatchConditions    addNewMetavariable  ( Metavariable       p_mv ) {
	return new MatchConditions ( instantiations, constraint, newMetavariables.add ( p_mv ), 
                                     renameTable );
    }
    
    public MatchConditions extendRenameTable() {        
        return new MatchConditions(instantiations, constraint, newMetavariables, 
                                   renameTable.extend());
    }    

    public MatchConditions addRenaming(QuantifiableVariable q1, QuantifiableVariable q2) {        
        return new MatchConditions(instantiations, constraint, newMetavariables, 
                                   renameTable.assign(q1, q2));
    }    
    
    public RenameTable renameTable() {
        return renameTable;
    }

    public MatchConditions shrinkRenameTable() {      
        return new MatchConditions(instantiations, constraint, newMetavariables, 
                                   renameTable.parent());
    }

    
}
