// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.util.Vector;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.strategy.Strategy;

public class JMLEclipseAdapter {
/*TODO
    KeYMediator mediator;
    Services services;
    String javaPath;
    ProgramMethod m=null;
    Implementation2SpecMap ism = null;
    JavaInfo ji;
    private boolean mainVisible=true;
    private Strategy strategy = null;

    public JMLEclipseAdapter(KeYMediator mediator){
       	services = mediator.getServices();
	ji = services.getJavaInfo();
	ism = services.getImplementation2SpecMap();
	this.mediator = mediator;
	javaPath = mediator.getProof().env().getJavaModel().getModelDir();
    }

    public Vector getMethodSpecs(String className, String methodName, 
				 ListOfString sigStrings){
	ListOfKeYJavaType signature = getSignature(sigStrings);
	KeYJavaType classType = ji.getKeYJavaTypeByClassName(className);
	m = ji.getProgramMethod(classType, methodName, signature, 
				classType);
	if(!m.getMethodDeclaration().isAbstract()){
	    SetOfJMLMethodSpec specs = 
		ism.getSpecsForMethod(m);
	    JMLClassSpec cSpec = ism.getSpecForClass(classType);
	    if(specs != null){
		specs = specs.union(services.getImplementation2SpecMap().
				    getInheritedMethodSpecs(m, classType));
	    }else{
		specs = ism.
		    getInheritedMethodSpecs(m, classType);
	    }
	    if(specs != SetAsListOfJMLMethodSpec.EMPTY_SET || cSpec != null){
		Vector specVector = new Vector();
		if(specs != null){
		    IteratorOfJMLMethodSpec it = specs.iterator();
		    while(it.hasNext()){
			JMLMethodSpec mSpec = it.next();
			specVector.add(mSpec);
			if(mSpec.replaceModelFieldsInAssignable() != null){
			    specVector.add(new AssignableCheckProofOblInput(
					       mSpec, javaPath));
			}
		    }
		}
		if(cSpec != null && (cSpec.containsInvOrConst())){
		    specVector.add(cSpec);
		}
		return specVector;
	    }
	}
	return null;
    }

    public void createPOandStartProver(JMLSpec spec, boolean allInv, 
				       boolean invPost, boolean assignable){
	ProofOblInput poi = null;
	if(spec instanceof JMLMethodSpec){
	    if(assignable){
		poi = new AssignableCheckProofOblInput((JMLMethodSpec) spec, 
						       javaPath);
		((AssignableCheckProofOblInput) poi).setAllInvariants(allInv);
	    }else if(invPost){
		poi = new JMLPostAndInvPO((JMLMethodSpec) spec, javaPath, 
				    allInv);
	    }else{
		poi = new JMLPostPO((JMLMethodSpec) spec, javaPath, allInv);
	    }
	}else if(spec instanceof JMLClassSpec){
	    poi = new JMLInvPO((JMLClassSpec) spec, m,
			       javaPath, allInv);
	}
	ProblemInitializer pi = new ProblemInitializer(Main.getInstance(mainVisible));
	try {
	    pi.startProver(mediator.getProof().env(), poi);
            if (getStrategy() != null) {
                mediator.getProof().setActiveStrategy(getStrategy());
            }
	} catch(ProofInputException e) {
	    //too bad
	}
    }

    private ListOfKeYJavaType getSignature(ListOfString l){
	de.uka.ilkd.key.collection.IteratorOfString it = l.iterator();
	ListOfKeYJavaType result = SLListOfKeYJavaType.EMPTY_LIST;
	while(it.hasNext()){
	    result = result.append(ji.getKeYJavaType(it.next()));
	}
	return result;
    }


    public void setMainVisible(boolean mainVisible) {
        this.mainVisible = mainVisible;
    }

    public void setStrategy(Strategy strategy) {
        this.strategy = strategy;
        
    }

    public Strategy getStrategy() {
        return strategy;
    }
    */
}
