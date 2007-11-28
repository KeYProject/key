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
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.logic.op.*;



public abstract class AbstractPVPrefixSkolemBuilder
    extends AbstractSkolemBuilder {

    private final ProgramVariablePrefixes prefixes;

    public AbstractPVPrefixSkolemBuilder
	( SkolemSet               p_oriSkolemSet,
	  ProgramVariablePrefixes p_prefixes,
	  Services                p_services ) {
	super ( p_oriSkolemSet, p_services );
	prefixes = p_prefixes;
    }

    protected ProgramVariablePrefixes getProgramVariablePrefixes () {
	return prefixes;
    }

    protected ListOfIProgramVariable getProgramVariablePrefix ( SchemaVariable p ) {
	ListOfIProgramVariable res = getProgramVariablePrefixes ().getPrefix ( p );
	if ( res == null )
	    res = SLListOfIProgramVariable.EMPTY_LIST;
	return res;
    }

    protected ArrayOfIProgramVariable getProgramVariablePrefixAsArray
	( SchemaVariable p ) {
	return getProgramVariablesAsArray
	    ( getProgramVariablePrefix ( p ) );
    }

    protected ArrayOfIProgramVariable getProgramVariablesAsArray
	( ListOfIProgramVariable p ) {

	int                       pvpSize = p.size ();

	IProgramVariable[]         pva     = new IProgramVariable [ pvpSize ];

	IteratorOfIProgramVariable it      = p.iterator ();

	int                       i       = 0;
	while ( it.hasNext () ) {
	    pva[i] = it.next ();
	    ++i;
	}

	return new ArrayOfIProgramVariable ( pva );
    }

    protected ArrayOfKeYJavaType getKeYJavaTypesAsArray
	( ListOfKeYJavaType p ) {

	int                   pvpSize = p.size ();

	KeYJavaType[]         pva     = new KeYJavaType [ pvpSize ];

	IteratorOfKeYJavaType it      = p.iterator ();

	int                   i       = 0;
	while ( it.hasNext () ) {
	    pva[i] = it.next ();
	    ++i;
	}

	return new ArrayOfKeYJavaType ( pva );
    }

    public ListOfIProgramVariable getProgramVariablesAsList
	( ArrayOfIProgramVariable p ) {

	ListOfIProgramVariable res = SLListOfIProgramVariable.EMPTY_LIST;

	int i = p.size ();
	while ( i-- != 0 )
	    res = res.prepend ( p.getIProgramVariable ( i ) );

	return res;

    }

    protected ListOfKeYJavaType getKeYJavaTypesAsList
	( ArrayOfKeYJavaType p ) {

	ListOfKeYJavaType res = SLListOfKeYJavaType.EMPTY_LIST;

	int i = p.size ();
	while ( i-- != 0 )
	    res = res.prepend ( p.getKeYJavaType ( i ) );

	return res;

    }

    protected ArrayOfKeYJavaType getProgramVariablePrefixTypes
	( SchemaVariable p ) {
	return getProgramVariableTypes
	    ( getProgramVariablePrefix ( p ) );
    }

    protected ArrayOfKeYJavaType getProgramVariableTypes
	( ListOfIProgramVariable p ) {

	int                       pvpSize  = p.size ();

	KeYJavaType[]             types    = new KeYJavaType [ pvpSize ];
	IteratorOfIProgramVariable it       = p.iterator ();

	int                       i        = 0;
	while ( it.hasNext () ) {
	    types[i] = it.next ().getKeYJavaType ();
	    ++i;
	}

	return new ArrayOfKeYJavaType ( types );
	
    }

}
