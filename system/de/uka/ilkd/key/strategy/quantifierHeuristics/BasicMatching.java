// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.MapAsListFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.MapFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;

class BasicMatching {
    
    private BasicMatching() {}
    
    /**
     * matching <code>trigger</code> to <code>targetTerm</code> recursively
     * @param trigger       a uni-trigger
     * @param targetTerm    a gound term
     * @return all substitution found from this matching
     */
    static SetOfSubstitution getSubstitutions(Term trigger, Term targetTerm) {
        SetOfSubstitution allsubs = SetAsListOfSubstitution.EMPTY_SET;
        if ( targetTerm.freeVars ().size () > 0
             || targetTerm.op () instanceof Quantifier ) return allsubs;
        final Substitution subst = match ( trigger, targetTerm );
        if ( subst != null ) allsubs = allsubs.add ( subst );
        final Operator op = targetTerm.op ();
        if ( !( op instanceof Modality || op instanceof IUpdateOperator ) ) {
            for ( int i = 0; i < targetTerm.arity (); i++ )
                allsubs =
                    allsubs.union ( getSubstitutions ( trigger,
                                                       targetTerm.sub ( i ) ) );
        }
        return allsubs;
    }
    
    /**
   	 * @param pattern
   	 * @param instance
   	 * @return all substitution that a given pattern(ex: a term of a uniTrigger)
   	 * match in the instance. 
   	 */
	private static Substitution match(Term pattern, Term instance) {
        final MapFromQuantifiableVariableToTerm map =
            matchRec ( MapAsListFromQuantifiableVariableToTerm.EMPTY_MAP,
                       pattern, instance );
        if ( map == null ) return null;
        return new Substitution ( map );
    }
        
	/**
	 * match the pattern to instance recursively.
	 */
	private static MapFromQuantifiableVariableToTerm
                   matchRec(MapFromQuantifiableVariableToTerm varMap,
                            Term pattern, Term instance) {
		final Operator patternOp = pattern.op ();
    
		if ( patternOp instanceof QuantifiableVariable )
			return mapVarWithCheck (varMap,
                                    (QuantifiableVariable)patternOp, instance);
        
		if ( patternOp != instance.op() ) return null;
        for ( int i = 0; i < pattern.arity (); i++ ) {
            varMap = matchRec ( varMap, pattern.sub ( i ), instance.sub ( i ) );
            if ( varMap == null ) return null;
        }
        return varMap;
	}

	/**
	 * match a variable to a instance. 
	 *  @return true if it is a new vaiable or the instance it matched is
     *  the same as that it matched before.
	 */
	private static MapFromQuantifiableVariableToTerm
                   mapVarWithCheck(MapFromQuantifiableVariableToTerm varMap,
                                   QuantifiableVariable var, Term instance) {
		final Term oldTerm = varMap.get ( var );
        if ( oldTerm == null ) return varMap.put ( var, instance );

        if ( oldTerm.equals ( instance ) ) return varMap;
        return null;
	}


}
