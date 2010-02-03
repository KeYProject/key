// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.Taclet;



/**
 * Create skolem symbols for term and formula schema variables
 */
public class FunctionSkolemBuilder extends AbstractPVPrefixSkolemBuilder {

    private final Namespace   skolemFunctions;
    private final Taclet      taclet;

    public FunctionSkolemBuilder ( Taclet                  p_taclet,
				   SkolemSet               p_oriSkolemSet,
				   ProgramVariablePrefixes p_prefixes,
				   Services                p_services ) {
	super ( p_oriSkolemSet, p_prefixes, p_services );

	taclet          = p_taclet;
	skolemFunctions = new Namespace ();
    }

    public IteratorOfSkolemSet build () {
	IteratorOfSchemaVariable it =
	    getOriginalSkolemSet ().getMissing ().iterator ();
	SchemaVariable           sv;

	while ( it.hasNext () ) {
	    sv = it.next ();

	    if ( sv.isTermSV () )
		createSkolemTermSV    ( (SortedSchemaVariable)sv );
	    else if ( sv.isFormulaSV () )
		createSkolemFormulaSV ( (SortedSchemaVariable)sv );
	}

	return toIterator
	    ( getOriginalSkolemSet ()
	      .add          ( getSVI() )
	      .addFunctions ( skolemFunctions ) );
    }

    private void addVocabulary(SkolemSymbolFactory p_factory) {
        skolemFunctions.add ( p_factory.getFunctions() );
    }

    private Term createSkolemFunction ( SortedSchemaVariable p_sv,
					Name                 p_name,
					Sort                 p_sort ) {

	final FunctionSkolemSymbolFactory f =
	    new FunctionSkolemSymbolFactory ( getServices() );
    
        final Term t = f.createFunctionSymbol(p_name,
				              p_sort,
				              createLogicArgs ( p_sv ),
				              getProgramVariablePrefix ( p_sv ));
          
        addVocabulary(f);
						
        return t;
    }

    // Very inefficient
    private ListOfTerm createLogicArgs ( SortedSchemaVariable p_sv ) {
	IteratorOfSchemaVariable it  = taclet.getPrefix ( p_sv ).iterator ();
	ListOfTerm               res = SLListOfTerm.EMPTY_LIST;

	while ( it.hasNext () )
	    res = res.append ( (Term)getSVI().getInstantiation ( it.next () ) );

	return res;
    }

    private void createSkolemTermSV ( SortedSchemaVariable p_sv ) {	

	if ( !isInstantiated ( p_sv ) ) {
	    final Name name = createUniqueName(p_sv.name ());
            addInstantiation( p_sv, createSkolemFunction ( p_sv,
							   name,
							   p_sv.sort () ) );
	}

    }

    private void createSkolemFormulaSV ( SortedSchemaVariable p_sv ) {
    	// currently formula skolem symbols are created just
    	// like function skolem symbols
	createSkolemTermSV ( p_sv );
    }

}
