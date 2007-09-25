// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.util.Vector;
import java.util.HashMap;

import de.uka.ilkd.key.java.declaration.ArrayOfParameterDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.jml.JMLSpec;
import de.uka.ilkd.key.jml.UsefulTools;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.util.Debug;

/** Represents a proof obligation for the assignable clause of a certain 
 * (jml) method specification case.
 * @deprecated Replaced by RespectsModifiesPO.
 */
public class AssignableCheckProofOblInput extends ModifiesCheckProofOblInput 
    implements JMLProofOblInput{

    private JMLMethodSpec spec;
    private String javaPath;

    private boolean allInv = false;

    public AssignableCheckProofOblInput(JMLMethodSpec spec, String javaPath){
	super("Assignable PO for: "+spec, null);
	this.javaPath = javaPath;
	this.spec = spec;
	location2descriptor = new HashMap();
    }

    public void setAllInvariants(boolean allInv){
	this.allInv = allInv;
    }

    public JMLSpec getSpec() {
        return spec;
    }

    private void createModifiesElements(){
        modifiesElements = SetAsListOfTerm.EMPTY_SET;
        SetOfLocationDescriptor locs = spec.replaceModelFieldsInAssignable();
	IteratorOfLocationDescriptor it = locs.iterator();
        while(it.hasNext()) {
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) it.next();
	    //            Debug.assertTrue(bloc.getFormula().equals(tf.createJunctorTerm(Op.TRUE)));
	    //            Debug.assertTrue(bloc.getLocTerm().freeVars().size() == 0);
	    location2descriptor.put(bloc.getLocTerm(), bloc);
            modifiesElements = modifiesElements.add(bloc.getLocTerm());
        }
    }

    public void readProblem(ModStrategy mod){
	createModifiesElements();
	MethodDeclaration md = spec.getMethodDeclaration();
	initConfig.progVarNS().add(UsefulTools.buildParamNamespace(md));
	initConfig.progVarNS().add(spec.getProgramVariableNS().allElements());
	if(spec.getMethodDeclaration().isStatic()){
	    self = null;
	}else{
	    self = (ProgramVariable) spec.getPrefix();
	}
	javaInfo = initConfig.getServices().getJavaInfo();
	createModifiesElements();
	pvVector = new Vector(md.getParameterDeclarationCount());
	ArrayOfParameterDeclaration ap = md.getParameters();
	for(int i=0; i<ap.size(); i++){
	    pvVector.add(ap.getParameterDeclaration(i).
			 getVariableSpecification().getProgramVariable());
	}
	m = spec.getProgramMethod();

	// puts all occuring classes into the set occuringClasses
	collectOccuringClasses(initConfig.getServices().getJavaInfo().
			       getKeYJavaType(spec.getClassDeclaration()));
	
	proofObl = TermFactory.DEFAULT.createJunctorTermAndSimplify(
	    Op.IMP, spec.getCompletePre(true, allInv, false), 
	    createProofStart());
	proofObl = UsefulTools.quantifyProgramVariables(proofObl, UsefulTools.buildParamNamespace(md).
	        allElements().iterator(), Op.ALL, initConfig.getServices());
	proofObl = spec.bindSpecVars(proofObl);
    }

    public boolean checkPurity(){
	return proofObl != null ? 
	    (UsefulTools.purityCheck(proofObl, initConfig.getServices().
				    getImplementation2SpecMap()) == null):
	    true;
    }

    /**
     * The Java Model is already initialized;
     */
    public String readModel(){
	return null;
    }

    /** returns the path to the Java model.
     */
    public String getJavaPath(){
	return javaPath;
    }

    public Contractable[] getObjectOfContract(){
        return new Contractable[]{spec.getProgramMethod()};
    }

    public boolean initContract(Contract ct) {
        return false; //%%
    }

    public void startProtocol() {
	// do nothing
    }

    public String createProgramVarsSection(){
	IteratorOfNamed it = initConfig.progVarNS().allElements().iterator();
	String result = "\\programVariables {\n";
	while(it.hasNext()){
	    ProgramVariable pv = (ProgramVariable) it.next();
	    result += pv.sort()+" "+pv.name()+";\n";
	}
	result += "}\n";
	return result;
    }

    public String createJavaSection(){
	return "\\javaSource \""+getJavaPath()+"\";\n";
    }

    public String createProblemHeader(){
	return createJavaSection()+"\n"+createProgramVarsSection()+"\n";
    }

    public ProofAggregate getPO(){
	return ProofAggregate.createProofAggregate(
	    new Proof(name(),
		      proofObl,
		      createProblemHeader(),
		      initConfig.createTacletIndex(), 
		      initConfig.createBuiltInRuleIndex(),
                      initConfig.getServices()), name());
    }

    public String toString(){
	return name();
    }

    public String name(){
	return "Assignable PO ("+(allInv ? "all invariants" : 
				  "only invariants from "+
				  spec.getClassDeclaration().
				  getName())+
	    ") for: "+spec;
    }

}
