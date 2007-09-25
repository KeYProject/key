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
import de.uka.ilkd.key.java.abstraction.Constructor;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;

public class JMLExceptionalMethodSpec extends JMLMethodSpec{

    public JMLExceptionalMethodSpec(ProgramMethod md, 
				Services services, 
				Namespace params, LinkedHashMap term2old, 
				JMLClassSpec cSpec, NamespaceSet nss, String javaPath){
	super(md, services, params, term2old, cSpec, nss, javaPath);
    }

    protected JMLExceptionalMethodSpec(){
	super();
    }

    /**
     * This is used for modelling specification inheritance for overwriten
     * methods.
     */
    public JMLMethodSpec cloneFor(ProgramMethod md, JMLClassSpec jmlClassSpec){
	if(!isCloneableFor(md)) return null;
	JMLExceptionalMethodSpec cloned = new JMLExceptionalMethodSpec();
	return cloneForHelper(cloned, md, jmlClassSpec);
    }

    public void addPost(Term t){}

    public Term getPost(){
	return ff();
    }

    public JMLMethodSpec copy(){
	JMLExceptionalMethodSpec copy = 
	    new JMLExceptionalMethodSpec(pm, services, params, 
					 term2old, cSpec, nss, getJavaPath());
	return copyHelper(copy);
    }

    public String toString(){
        return toStringHelper("exceptional_behavior speccase");
    }

    public Term getCompletePost(boolean withClassSpec, boolean allInv){
	if(lv2old == null){
	    getPi1();
	}
	Term result = 
	    createModalityTermForEnsures(ff(), false, withClassSpec, allInv).sub(0);
	result = addOldQuantifiers(result, lv2old, false, params);
	if(!(pm.getMethodDeclaration() instanceof Constructor)){
	    result = updatePrefix(result);
	}
	return result;
    }

}

