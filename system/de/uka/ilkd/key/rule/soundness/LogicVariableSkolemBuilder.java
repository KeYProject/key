// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;



/**
 * Create logical variables as skolem symbols for variable schema
 * variables
 */
public class LogicVariableSkolemBuilder extends AbstractSkolemBuilder {

    public LogicVariableSkolemBuilder ( SkolemSet p_oriSkolemSet,
                                        Services  p_services ) {
	super ( p_oriSkolemSet, p_services );
    }
    
    public IteratorOfSkolemSet build () {
	IteratorOfSchemaVariable it =
	    getOriginalSkolemSet ().getMissing ().iterator ();
	SchemaVariable           sv;

	while ( it.hasNext () ) {
	    sv = it.next ();

	    if ( sv.isVariableSV () )
		createSkolemVariableSV ( (SortedSchemaVariable)sv );
	}

	return toIterator
	    ( getOriginalSkolemSet ().add ( getSVI() ) );
    }

    private void createSkolemVariableSV ( SortedSchemaVariable p_sv ) {	

	if ( !isInstantiated(p_sv) ) {
            Name          name = createUniqueName(p_sv.name());
	    LogicVariable var  = new LogicVariable ( name, p_sv.sort () );
	    Term          term = getTF().createVariableTerm ( var );

            addInstantiation(p_sv, term);
	}


    }

}
