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

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.statement.JumpStatement;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.ListOfIProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.ListOfTacletApp;
import de.uka.ilkd.key.rule.SLListOfTacletApp;
import de.uka.ilkd.key.util.ExtList;



/**
 * Abstract class that provides some methods both the statement and the
 * expression skolem builder need
 */
public abstract class StatementExpressionSkolemBuilder
    extends AbstractPVPrefixSkolemBuilder {

    private final Namespace skolemVariables = new Namespace ();
    private ListOfTacletApp taclets         = SLListOfTacletApp.EMPTY_LIST;

    private final JumpStatementPrefixes  jumpStatementPrefixes;


    public StatementExpressionSkolemBuilder
	( SkolemSet               p_oriSkolemSet,
	  ProgramVariablePrefixes p_prefixes,
	  JumpStatementPrefixes   p_jumpStatementPrefixes,
	  Services                p_services ) {
	super ( p_oriSkolemSet, p_prefixes, p_services );

	jumpStatementPrefixes = p_jumpStatementPrefixes;
    }

    protected JumpStatementPrefixes getJumpStatementPrefixes () {
	return jumpStatementPrefixes;
    }

    protected ListOfStatement getJumpStatementPrefix ( SchemaVariable p ) {
	ListOfStatement res = getJumpStatementPrefixes ().getPrefix ( p );
	if ( res == null )
	    res = SLListOfStatement.EMPTY_LIST;
	return res;
    }


    protected ListOfTacletApp getTaclets() {
        return taclets;
    }

    protected void addVocabulary(SkolemSymbolTacletFactory p_factory) {
	// We only have to add variables and taclets, as no other symbols are
	// currently created by the concerned factories 
        skolemVariables.add ( p_factory.getVariables() );
        this.taclets = taclets.prepend ( p_factory.getTaclets() );	
    }

    protected Namespace getVariables() {
        return skolemVariables;
    }


    protected class StatementSymbolArgBuilder {

	private final SchemaVariable   sv;
        private ListOfIProgramVariable pvp;
	private ArrayOfStatement       jt;

	StatementSymbolArgBuilder ( SchemaVariable p_sv ) {
	    sv  = p_sv;
	    pvp = getProgramVariablePrefix(sv);
	    jt  = createJumpTable();
	}

	ListOfIProgramVariable getInfluencingPVs () {
	    return pvp;
	}

        ArrayOfStatement getJumpTable() {
            return jt;
        }

	private ArrayOfStatement createJumpTable () {
	    ExtList res = new ExtList ();

	    //	try { // <-- why this??
	    {
		KeYJavaType     th =
		    getJavaInfo ().getTypeByClassName ( "java.lang.Throwable" );
		ProgramVariable v  = new LocationVariable
		    ( createUniquePEName("th"), th );

		JumpStatement   js = new Throw ( v );

		res.add ( js );
		pvp = pvp.prepend ( v );
		getVariables().add ( v );
	    }
	    //	} catch ( RuntimeException e ) {}

	    IteratorOfStatement it = getJumpStatementPrefix ( sv ).iterator ();
	    Statement           s;
	    while ( it.hasNext () ) {
		s = it.next ();
	    
		if ( s instanceof Return ) {
		    Expression e = ((Return)s).getExpression ();
		    if ( e instanceof SchemaVariable ) {
			// this one should already have been instantiated
			ProgramElement pe       =
			    (ProgramElement)getOriginalSkolemSet ()
			    .getInstantiations ()
			    .getInstantiation ( (SchemaVariable)e );
		    
			if ( pe != null ) {
			    ExtList children = new ExtList ();
			    children.add ( pe );
			    s = new Return ( children );
			}
		    }
		}

		res.add ( s );
	    }

	    return new ArrayOfStatement ( (Statement[])res.collect
					  ( Statement.class ) );	
	}

    }	
}
