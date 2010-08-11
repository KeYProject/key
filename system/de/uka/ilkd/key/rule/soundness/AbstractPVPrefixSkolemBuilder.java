// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.rule.soundness;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;



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

    protected ImmutableList<IProgramVariable> getProgramVariablePrefix ( SchemaVariable p ) {
	ImmutableList<IProgramVariable> res = getProgramVariablePrefixes ().getPrefix ( p );
	if ( res == null )
	    res = ImmutableSLList.<IProgramVariable>nil();
	return res;
    }

    protected ImmutableArray<IProgramVariable> getProgramVariablePrefixAsArray
	( SchemaVariable p ) {
	return getProgramVariablesAsArray
	    ( getProgramVariablePrefix ( p ) );
    }

    protected ImmutableArray<IProgramVariable> getProgramVariablesAsArray
	( ImmutableList<IProgramVariable> p ) {

	int                       pvpSize = p.size ();

	IProgramVariable[]         pva     = new IProgramVariable [ pvpSize ];

	Iterator<IProgramVariable> it      = p.iterator ();

	int                       i       = 0;
	while ( it.hasNext () ) {
	    pva[i] = it.next ();
	    ++i;
	}

	return new ImmutableArray<IProgramVariable> ( pva );
    }

    protected ImmutableArray<KeYJavaType> getKeYJavaTypesAsArray
	( ImmutableList<KeYJavaType> p ) {

	int                   pvpSize = p.size ();

	KeYJavaType[]         pva     = new KeYJavaType [ pvpSize ];

	Iterator<KeYJavaType> it      = p.iterator ();

	int                   i       = 0;
	while ( it.hasNext () ) {
	    pva[i] = it.next ();
	    ++i;
	}

	return new ImmutableArray<KeYJavaType> ( pva );
    }

    public ImmutableList<IProgramVariable> getProgramVariablesAsList
	( ImmutableArray<IProgramVariable> p ) {

	ImmutableList<IProgramVariable> res = ImmutableSLList.<IProgramVariable>nil();

	int i = p.size ();
	while ( i-- != 0 )
	    res = res.prepend ( p.get ( i ) );

	return res;

    }

    protected ImmutableList<KeYJavaType> getKeYJavaTypesAsList
	( ImmutableArray<KeYJavaType> p ) {

	ImmutableList<KeYJavaType> res = ImmutableSLList.<KeYJavaType>nil();

	int i = p.size ();
	while ( i-- != 0 )
	    res = res.prepend ( p.get ( i ) );

	return res;

    }

    protected ImmutableArray<KeYJavaType> getProgramVariablePrefixTypes
	( SchemaVariable p ) {
	return getProgramVariableTypes
	    ( getProgramVariablePrefix ( p ) );
    }

    protected ImmutableArray<KeYJavaType> getProgramVariableTypes
	( ImmutableList<IProgramVariable> p ) {

	int                       pvpSize  = p.size ();

	KeYJavaType[]             types    = new KeYJavaType [ pvpSize ];
	Iterator<IProgramVariable> it       = p.iterator ();

	int                       i        = 0;
	while ( it.hasNext () ) {
	    types[i] = it.next ().getKeYJavaType ();
	    ++i;
	}

	return new ImmutableArray<KeYJavaType> ( types );
	
    }

}
