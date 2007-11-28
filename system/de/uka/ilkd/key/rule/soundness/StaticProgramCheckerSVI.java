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

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class StaticProgramCheckerSVI extends StaticProgramChecker {

    private SVInstantiations svi;

    public StaticProgramCheckerSVI ( ProgramElement   p_root,
				     SVInstantiations p_svi,
				     Services         p_services ) {
	super ( p_root, p_services );
	svi = p_svi;
    }


    public SVInstantiations getSVInstantiations () {
	return svi;
    }


    public void doSchemaVariable(SchemaVariable x)     {
	// todo: handle some special sv sorts, whose type is
	// determined without instantiation
	if ( getSVInstantiations ().isInstantiated ( x ) ) {
	    walk ( (ProgramElement)getSVInstantiations ()
		   .getInstantiation ( x ) );
	} else
	    pushUnknown ();
    }

}
