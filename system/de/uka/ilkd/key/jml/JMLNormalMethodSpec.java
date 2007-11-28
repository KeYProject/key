// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/** A normal jml methodspecification declared by the jml-keyword 
    <code>normal_behavior</code>*/
public class JMLNormalMethodSpec extends JMLMethodSpec {
    
    public JMLNormalMethodSpec(ProgramMethod pm, Services services, 
            Namespace params, LinkedHashMap term2old, JMLClassSpec cSpec, 
            NamespaceSet nss, String javaPath) {
	
        super(pm, services, params, term2old, cSpec, nss, javaPath);
	addSignals(exc, null, ff());
    
    }

    protected JMLNormalMethodSpec(){
	super();
    }

    /**
     * This is used for modelling specification inheritance for overwriten
     * methods.
     */
    public JMLMethodSpec cloneFor(ProgramMethod method, JMLClassSpec jmlClassSpec){
	if(!isCloneableFor(method)) return null;
	JMLNormalMethodSpec cloned = new JMLNormalMethodSpec();
	return cloneForHelper(cloned, method, jmlClassSpec);
    }

    public ProgramElement getProofStatement(){
	return makeMBS().getStatementAt(0);
    }

    protected Term createModalityTermForEnsures(Term post, boolean desugar,
						boolean withInv, 
						boolean allInv){
	ModTermKey key = new ModTermKey(post, desugar, withInv, allInv);
	Term c = (Term) modalityTermForEnsuresCache.get(key);
	if(c != null){
	    return c;
	}
	if(diverges == null || ff().equals(diverges)){
	    JavaBlock jb = 
		JavaBlock.createJavaBlock(new StatementBlock(makeMBS()));
	    if(withInv && !services.getImplementation2SpecMap().
	       getModifiers(pm).contains("helper")){
		post = cSpec.addClassSpec2Post(post, true, !allInv, pm, cSpec);
		if(allInv){
		    Term ai = UsefulTools.allInvariants(
			services.getImplementation2SpecMap());
		    if(ai != null){
			post = and ( ai, post );
		    }
		}
	    }
	    post = updatePrefix(post);
	    post = UsefulTools.addRepresents(post, services,(ProgramVariable)
					     cSpec.getInstancePrefix());
	    c = dia(jb, post);
	}else{
	    final Term excVarTerm = var(excVar);
	    post = and ( equals(excVarTerm, nullTerm), post);
	    final JavaBlock jb = catchAllJB(desugar);
	    
            if(withInv && !services.getImplementation2SpecMap().
	       getModifiers(pm).contains("helper")){
		post = cSpec.addClassSpec2Post(post, true, !allInv, pm, cSpec);
		if(allInv){
		    Term ai = UsefulTools.allInvariants(
			services.getImplementation2SpecMap());
		    if(ai != null){
			post = and(ai, post);
		    }
		}
	    }
	    post = updatePrefix(post);
	    post = UsefulTools.addRepresents(post, services,(ProgramVariable)
					     cSpec.getInstancePrefix());
	    c = box(jb, post);
	}
	modalityTermForEnsuresCache.put(key, c);
	return c;
    }

    public JMLMethodSpec copy(){
	final JMLNormalMethodSpec copy = 
	    new JMLNormalMethodSpec(pm, services, params, 
				    term2old, cSpec, nss, getJavaPath());
	return copyHelper(copy);
    }

    public String toString(){
        return toStringHelper("normal_behavior speccase");
    }
}

