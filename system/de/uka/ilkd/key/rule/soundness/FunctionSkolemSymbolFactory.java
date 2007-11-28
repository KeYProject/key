// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.ListOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfIProgramVariable;
import de.uka.ilkd.key.logic.op.ListOfIProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.ExtList;

/**
 * Factory to create skolem symbols for terms
 */
public class FunctionSkolemSymbolFactory extends SkolemSymbolFactory {

    public FunctionSkolemSymbolFactory(Services p_services) {
        super(p_services);
    }

    public Term createFunctionSymbol( Name                   p_name,
				      Sort                   p_sort,
				      ListOfTerm             p_logicArgs,
				      ListOfIProgramVariable p_influencingPVs ) {
	Term[] logicArgs = toArray ( p_logicArgs );
	Term[] pvArgs    = createPVArgs ( p_influencingPVs );
        
        Term[] realArgs  = new Term [ logicArgs.length + pvArgs.length ];
        
        System.arraycopy(logicArgs, 0, realArgs, 0,                logicArgs.length);
        System.arraycopy(pvArgs,    0, realArgs, logicArgs.length, pvArgs.length);
        
        SVSkolemFunction f = new SVSkolemFunction
            ( p_name, p_sort,
              new ArrayOfSort ( sortsOf(logicArgs) ),
              getProgramVariableTypes ( p_influencingPVs ) );
        addFunction ( f );
        
        return getTF().createFunctionTerm ( f, realArgs );
    }

    // Very inefficient
    private Term[] createPVArgs(ListOfIProgramVariable pvp) {
        IteratorOfIProgramVariable it  = pvp.iterator ();
	ExtList                    res = new ExtList ();

	while ( it.hasNext () )
	    res.add
	        ( getTF().createVariableTerm ( (ProgramVariable)it.next () ) );

	return (Term[])res.collect ( Term.class );
    }

    // Very inefficient
    private Term[] toArray(ListOfTerm p_list) {
        IteratorOfTerm it  = p_list.iterator ();
	ExtList        res = new ExtList ();

	while ( it.hasNext () )
	    res.add ( it.next () );

	return (Term[])res.collect ( Term.class );
    }

    private Sort[] sortsOf(Term[] p_terms) {
        Sort[] res  = new Sort [ p_terms.length ];
        
        int j;
        for ( j = 0; j != p_terms.length; ++j )
            res[j] = p_terms[j].sort ();
            
        return res;
    }

}
