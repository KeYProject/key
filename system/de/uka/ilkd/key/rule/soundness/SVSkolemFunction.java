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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.sort.Sort;



public class SVSkolemFunction extends NonRigidFunction
    implements StateDependingObject {


    private ImmutableArray<KeYJavaType> influencingPVTypes;


    public SVSkolemFunction ( Name               name,
			      Sort               sort,
			      ImmutableArray<Sort>        argSorts,
			      ImmutableArray<KeYJavaType> influencingPVTypes ) {
	super ( name, sort, effectiveArgs ( argSorts, influencingPVTypes ) );
	this.influencingPVTypes = influencingPVTypes;
    }    


    public ImmutableArray<KeYJavaType> getInfluencingPVTypes () {
	return influencingPVTypes;
    }


    private static ImmutableArray<Sort> effectiveArgs
	( ImmutableArray<Sort>        argSorts,
	  ImmutableArray<KeYJavaType> influencingPVTypes ) {
	Sort[] res = new Sort [ argSorts.size () + influencingPVTypes.size () ];

	int j;
	for ( j = 0; j != argSorts.size (); ++j )
	    res[j] = argSorts.get ( j );

	int i;
	for ( i = 0; i != influencingPVTypes.size (); ++i, ++j )
	    res[ j ] = influencingPVTypes.get ( i ).getSort ();

	return new ImmutableArray<Sort> ( res );
    }
}
