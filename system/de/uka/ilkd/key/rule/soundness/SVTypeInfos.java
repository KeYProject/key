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

import de.uka.ilkd.key.logic.op.SchemaVariable;


/**
 * Immutable
 */
public class SVTypeInfos {

    public static final SVTypeInfos EMPTY_SVTYPEINFOS =
	new SVTypeInfos ( SLListOfSVTypeInfo.EMPTY_LIST );

    private ListOfSVTypeInfo infos;

    private SVTypeInfos ( ListOfSVTypeInfo p_infos ) {
	infos = p_infos;
    }

    public SVTypeInfos addInfo ( SVTypeInfo p ) {
	SVTypeInfo old = getInfo ( p.getSV () );

	if ( old != null ) {
	    if ( old.equals ( p ) )
		return this;
	    else
		throw new InvalidPrefixException
		    ( "Invalid types given for schema variable (perhaps TODO)" );		    
	}

	return new SVTypeInfos ( infos.prepend ( p ) );
    }

    public SVTypeInfo getInfo ( SchemaVariable p ) {
	IteratorOfSVTypeInfo it   = infos.iterator ();
	SVTypeInfo           info;

	while ( it.hasNext () ) {
	    info = it.next ();
	    if ( info.getSV () == p )
		return info;
	}

	return null;
    }

    public String toString () {
	return "" + infos;
    }
}
