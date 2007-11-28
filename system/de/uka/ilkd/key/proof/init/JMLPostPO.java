// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.jml.UsefulTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;

public class JMLPostPO extends JMLProofOblInputImpl{

    private Term po = null;

    public JMLPostPO(JMLMethodSpec spec, String javaPath, boolean allInv){
	super(spec, javaPath, allInv);
	pm = spec.getProgramMethod();
    }

    public ProofAggregate getPO(){
	return ProofAggregate.createProofAggregate(
	    new Proof(name(),
		      po,
		      createProblemHeader(),
		      initConfig.createTacletIndex(), 
		      initConfig.createBuiltInRuleIndex(),
                      initConfig.getServices()), name());
    }

    public void readProblem(ModStrategy mod) throws ProofInputException{
	initConfig.progVarNS().add(UsefulTools.buildParamNamespace(pm.getMethodDeclaration()));

	po = ((JMLMethodSpec) spec).createDLFormula(false, allInv);
        
	initConfig.progVarNS().add(spec.getProgramVariableNS().allElements());
	if(allInv){
	    initConfig.progVarNS().add(initConfig.getServices().
				       getImplementation2SpecMap().
				       getAllInvPVNS().allElements());
	}
    }
    
    public boolean checkPurity(){
	return UsefulTools.purityCheck((JMLMethodSpec) spec, 
				       initConfig.getServices().
				       getImplementation2SpecMap()) == null;
    }

    public String name(){
	return "Ensures Post Condition PO (using "+
	    (allInv ? "all invariants" : "only invariants from "+
	     ((JMLMethodSpec) spec).getClassDeclaration().getName())+
	    " for the precondition) Condition PO for:\n "+spec.toString();
    }

}
