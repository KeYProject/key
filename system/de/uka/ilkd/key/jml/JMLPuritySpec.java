// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.jml;

import java.util.LinkedHashMap;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.ProgramMethod;
 
/**
 * A generic method spec used to desugar the pure modifier:
 *
 *     behavior
 *        assignable \nothing;
 */
public class JMLPuritySpec extends JMLMethodSpec{

    public JMLPuritySpec(ProgramMethod md,  
			 Services services, Namespace params, 
			 LinkedHashMap term2old, JMLClassSpec cSpec, 
			 NamespaceSet nss, String javaPath){
	super(md, services, params, term2old, cSpec, nss, javaPath);
	this.setAssignableMode("nothing");
    }

    public String toString(){
	return "Purity specification for method "+pm.getName()+
	    " \nin context "+cd.getName();
    }
}
