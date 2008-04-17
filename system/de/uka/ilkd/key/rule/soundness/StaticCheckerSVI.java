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

import org.apache.log4j.Logger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;


public class StaticCheckerSVI extends StaticChecker {

    private SVInstantiations svi;

    public StaticCheckerSVI ( SVInstantiations p_svi,
			      Services         p_services ) {
	super ( p_services );
	svi = p_svi;
    }


    public SVInstantiations getSVInstantiations () {
	return svi;
    }


    public void check ( Term p_term ) {
	SyntacticalReplaceVisitor srv =
	    new SyntacticalReplaceVisitor ( getServices (), 
					    getSVInstantiations (),
					    Constraint.BOTTOM,
					    false, null,
					    true, false );

	p_term.execPostOrder ( srv );
	
	srv.getTerm ().execPostOrder ( this );
    }


    public static boolean isValidType ( Term             p_formula,
					SVInstantiations p_current,
					SchemaVariable   p_sv,
					KeYJavaType      p_type,
					Services         p_services ) {
	return isValidType ( p_formula,
			     p_current, 
			     SLListOfSchemaVariable.EMPTY_LIST.prepend ( p_sv ),
			     p_type,
			     p_services );
    }

    public static boolean isValidType ( Term                 p_formula,
					SVInstantiations     p_current,
					ListOfSchemaVariable p_svs,
					KeYJavaType          p_type,
					Services             p_services ) {

	return isValidType ( p_formula,
			     p_current,
			     p_svs,
			     new LocationVariable
			     ( new ProgramElementName ( "x" ), p_type ),
			     p_services );
    }

    public static boolean isValidType ( Term                 p_formula,
					SVInstantiations     p_current,
					ListOfSchemaVariable p_svs,
					IProgramVariable     p_pv,
					Services             p_services ) {

        Logger.getLogger ( "key.taclet_soundness" ).debug ( "isValidType() with "
                + p_pv );

	try {
	    StaticCheckerSVI sc =
		new StaticCheckerSVI ( addInstantiation ( p_current,
							  p_svs,
							  p_pv,
							  0 ),
				       p_services );
	    sc.check ( p_formula );

	    return true;
	} catch ( StaticTypeException e ) {
	    //	    e.printStackTrace ();
	    Debug.out("Exception thrown by class StaticCheckerSVI at check()");
	}
	
	return false;
    }

    public static SVInstantiations
	addInstantiation ( SVInstantiations     p_current,
			   ListOfSchemaVariable p_svs,
			   IProgramVariable     p_pv,
			   int                  p_instantiationType ) {
	IteratorOfSchemaVariable svIt;
	for ( svIt = p_svs.iterator (); svIt.hasNext (); )
	    p_current = p_current.add ( svIt.next (), p_pv,
					p_instantiationType );

	return p_current;	
    }

}
