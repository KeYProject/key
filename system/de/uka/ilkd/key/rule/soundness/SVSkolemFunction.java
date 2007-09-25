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

import de.uka.ilkd.key.java.abstraction.ArrayOfKeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.sort.ArrayOfSort;
import de.uka.ilkd.key.logic.sort.Sort;



public class SVSkolemFunction extends NonRigidFunction
    implements StateDependingObject {


    private ArrayOfKeYJavaType influencingPVTypes;


    public SVSkolemFunction ( Name               name,
			      Sort               sort,
			      ArrayOfSort        argSorts,
			      ArrayOfKeYJavaType influencingPVTypes ) {
	super ( name, sort, effectiveArgs ( argSorts, influencingPVTypes ) );
	this.influencingPVTypes = influencingPVTypes;
    }    


    public ArrayOfKeYJavaType getInfluencingPVTypes () {
	return influencingPVTypes;
    }


    private static ArrayOfSort effectiveArgs
	( ArrayOfSort        argSorts,
	  ArrayOfKeYJavaType influencingPVTypes ) {
	Sort[] res = new Sort [ argSorts.size () + influencingPVTypes.size () ];

	int j;
	for ( j = 0; j != argSorts.size (); ++j )
	    res[j] = argSorts.getSort ( j );

	int i;
	for ( i = 0; i != influencingPVTypes.size (); ++i, ++j )
	    res[ j ] = influencingPVTypes.getKeYJavaType ( i ).getSort ();

	return new ArrayOfSort ( res );
    }

    /**
     * @return true if the value of "term" having this operator as
     * top-level operator and must not be changed by modalities
     */
    public boolean isRigid (Term term) {
	return false;
    }

}
