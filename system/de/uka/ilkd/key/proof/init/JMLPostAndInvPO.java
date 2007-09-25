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

package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.jml.UsefulTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.proof.mgt.JMLMethodContract;
import de.uka.ilkd.key.proof.mgt.JavaModelMethod;

public class JMLPostAndInvPO extends JMLProofOblInputImpl{

    private Term po = null;
    private JavaModelMethod jmm = null;
    private ProofAggregate result;

    public JMLPostAndInvPO(JMLMethodSpec spec, String javaPath, boolean allInv){
	super(spec, javaPath, allInv);
	pm = spec.getProgramMethod();
	jmm = new JavaModelMethod(spec.getProgramMethod(), javaPath, null); //TODO
    }

    public ProofAggregate getPO(){
        if (result!=null) return result;
        return result = ProofAggregate.createProofAggregate(
                new Proof(name(),
                        po,
                        createProblemHeader(),
                        initConfig.createTacletIndex(), 
                        initConfig.createBuiltInRuleIndex(),
                        initConfig.getServices()), name());
    }

    public void readProblem(ModStrategy mod) throws ProofInputException{
	initConfig.progVarNS().
	    add(UsefulTools.buildParamNamespace(pm.getMethodDeclaration()));
	po = ((JMLMethodSpec) spec).createDLFormula(true, allInv);
        initConfig.progVarNS().add(spec.getProgramVariableNS().allElements());
	if(allInv){
	    initConfig.progVarNS().add(initConfig.getServices().
				       getImplementation2SpecMap().
				       getAllInvPVNS().allElements());
	}
    }

    public boolean initContract(Contract ct) {
        if (!(ct instanceof JMLMethodContract) || allInv!=JMLMethodContract.allInvariants) {
            return false;
        }
        if (((JMLMethodContract) ct).getSpec() != spec) {
            return false;
        }
        ct.addCompoundProof(getPO());
        return true;
    }

    public boolean checkPurity(){
	return po != null ? 
	    (UsefulTools.purityCheck(po, initConfig.getServices().
				    getImplementation2SpecMap()) == null):
	    true;
    }

    public Contractable[] getObjectOfContract(){
        return new Contractable[]{jmm};
    }

    public String name(){
	return "Post, Invariant "+(allInv ? "(including all invariants)" : 
				  "(only invariants for "+
				  ((JMLMethodSpec) spec).
				   getClassDeclaration().getName()+")")+
	    " and Constraint PO for spec:\n "+
	    spec.toString();
    }

}
