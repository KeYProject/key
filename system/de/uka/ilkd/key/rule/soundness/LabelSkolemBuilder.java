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
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;



/**
 * Create skolem symbols (labels) for schema variables for labels.
 */
public class LabelSkolemBuilder extends AbstractSkolemBuilder {

    public LabelSkolemBuilder ( SkolemSet p_oriSkolemSet, Services p_services ) {
	super ( p_oriSkolemSet, p_services );
    }
    
    public IteratorOfSkolemSet build () {
	IteratorOfSchemaVariable it =
	    getOriginalSkolemSet ().getMissing ().iterator ();
	SchemaVariable           sv;

	while ( it.hasNext () ) {
	    sv = it.next ();

	    if ( sv.isProgramSV () &&
		 ((SortedSchemaVariable)sv).sort () == ProgramSVSort.LABEL )
		createSkolemLabel ( sv );
	}

	return toIterator
	    ( getOriginalSkolemSet ().add ( getSVI() ) );
    }

    private void createSkolemLabel ( SchemaVariable p_sv ) {	
	if ( !isInstantiated ( p_sv ) ) {
	    ProgramElementName name = createUniquePEName ( p_sv.name () );
	    addInstantiation(p_sv, name);
	}

    }

}
