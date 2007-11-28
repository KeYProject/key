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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;


public class StaticChecker extends TacletVisitor {

    Services services;

    public StaticChecker ( Services p_services ) {
	services = p_services;
    }


    public Services  getServices () {
	return services;
    }


    // VISITOR RELATED METHODS

    public void subtreeEntered(Term t) {
    }

    /** is called by the execPostOrder-method of a term 
     * @param Term to checked if it is a Variable and if true the
     * Variable is added to the list of found Variables
     */  
    public void visit(Term t) {	
	if ( t.op() instanceof Modality )
	    callProgramChecker ( t );
    }

    protected void callProgramChecker ( Term p_term ) {
	StaticProgramChecker c = new StaticProgramChecker
	    ( p_term.javaBlock ().program (), getServices () );
	c.start ();
    }

}
