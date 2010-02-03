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

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.SyntacticalReplaceVisitor;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public class SVPrefixCollectorSVI extends SVPrefixCollector {

    private SVInstantiations svi;

    public SVPrefixCollectorSVI ( SVInstantiations p_svi,
				  SVTypeInfos      p_svTypeInfos,
				  Services         p_services ) {
	super ( p_svTypeInfos, p_services );
	svi = p_svi;
    }


    public SVInstantiations getSVInstantiations () {
	return svi;
    }


    public void collect ( Term p_term ) {
	SyntacticalReplaceVisitor srv =
	    new SyntacticalReplaceVisitor ( getServices (), 
					    getSVInstantiations (),
					    Constraint.BOTTOM,
					    false, null,
					    true, false );

	p_term.execPostOrder ( srv );
	
	srv.getTerm ().execPostOrder ( this );
    }

}
