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

import de.uka.ilkd.key.jml.JMLClassSpec;
import de.uka.ilkd.key.jml.UsefulTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.Contract;

/** the proofobligation for invariants and historyconstraints*/
public class JMLInvPO extends JMLProofOblInputImpl{

    private Term po = null;

    public JMLInvPO(JMLClassSpec spec, ProgramMethod pm,
		    String javaPath, boolean allInv){
	super(spec, javaPath, allInv);
	this.pm = pm;
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
	po = ((JMLClassSpec) spec).getPreservesInvariantBehavior(pm, allInv);
        initConfig.progVarNS().add(spec.getProgramVariableNS().allElements());
	if(allInv){
	    initConfig.progVarNS().add(initConfig.getServices().
				       getImplementation2SpecMap().
				       getAllInvPVNS().allElements());
	}
    }

    public boolean initContract(Contract ct){
        return false;
    }

    public String name(){
	return "Invariant "+(allInv ? "(including all invariants)" : 
			     "(only invariants for "+
			     ((JMLClassSpec) spec).
			     getClassDeclaration().getName()+")")+
	    " and History Constraint PO for "+
	    pm.getMethodDeclaration().getName(); 
    }

    public boolean checkPurity(){
	return po != null ? 
	    (UsefulTools.purityCheck(po, initConfig.getServices().
				    getImplementation2SpecMap()) == null):
	    true;
    }

}
