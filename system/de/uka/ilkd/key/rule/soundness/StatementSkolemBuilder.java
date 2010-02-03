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

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.ArrayOfStatement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.IteratorOfSchemaVariable;
import de.uka.ilkd.key.logic.op.ListOfIProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;



/**
 * Create statement skolem symbols to instantiate schema variables for
 * statements
 */
public class StatementSkolemBuilder
    extends StatementExpressionSkolemBuilder {

    public StatementSkolemBuilder
	( SkolemSet               p_oriSkolemSet,
	  ProgramVariablePrefixes p_prefixes,
	  JumpStatementPrefixes   p_jumpStatementPrefixes,
	  Services                p_services ) {
	super ( p_oriSkolemSet,
		p_prefixes,
		p_jumpStatementPrefixes,
		p_services );
    }

    public IteratorOfSkolemSet build () {
	IteratorOfSchemaVariable it =
	    getOriginalSkolemSet ().getMissing ().iterator ();

	while ( it.hasNext () ) {
	    final SchemaVariable sv = it.next ();

	    if ( sv.isProgramSV () &&
		 ((SortedSchemaVariable)sv).sort () ==
		     ProgramSVSort.STATEMENT &&
		 !isInstantiated ( sv ) )
	        createSkolemStatementSV ( sv );
	}

	return toIterator
	    ( getOriginalSkolemSet ()
	      .add          ( getSVI() )
	      .addVariables ( getVariables() )
	      .addTaclets   ( getTaclets() ) );
    }

    private void createSkolemStatementSV ( SchemaVariable p_sv ) {
	Logger.getLogger ( "key.taclet_soundness" )
	        .debug ( "createSkolemStatementSV() with " + p_sv );

	final StatementSymbolArgBuilder b =
	    new StatementSymbolArgBuilder ( p_sv );	
	final ProgramSVProxy proxy =
	    createStatementSymbol("" + p_sv.name (),
				  b.getInfluencingPVs(),
				  b.getJumpTable());
	addInstantiation(p_sv, proxy);
    }

    private ProgramSVProxy
	createStatementSymbol ( String                 baseName,
				ListOfIProgramVariable p_pvArgs,
				ArrayOfStatement       jumpTable) {
	final StatementSkolemSymbolFactory f =
	    new StatementSkolemSymbolFactory ( getServices() );
    
        final ProgramSVProxy proxy =
            f.createStatementSymbol(createUniquePEName(baseName),
                                    p_pvArgs,
                                    jumpTable);
          
        addVocabulary(f);
        
        return proxy;
    }

}
