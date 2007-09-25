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

import de.uka.ilkd.key.java.abstraction.ArrayType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.jml.JMLSpec;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.proof.mgt.JavaModelMethod;
import de.uka.ilkd.key.util.KeYExceptionHandler;


public abstract class JMLProofOblInputImpl implements JMLProofOblInput {

    protected JMLSpec spec = null;
    protected ProgramMethod pm = null;
    protected InitConfig initConfig = null;
    protected String javaPath = null;
    protected KeYExceptionHandler exceptionHandler = null;
    protected boolean allInv = false;

    protected JMLProofOblInputImpl(JMLSpec spec, String javaPath, 
				   boolean allInv){
	this.spec = spec;
	this.javaPath = javaPath;
        this.allInv = allInv;
    }

    /**
     * sets the exception handler used to collect occured errors
     */
    public void setExceptionHandler(KeYExceptionHandler keh){
	exceptionHandler = keh;
    }

    public boolean initContract(Contract ct) {
        return false;
    }

    public boolean askUserForEnvironment(){
	return false;
    }

    /**
     * Checks if the methods used in the specification that underlies this
     * JMLProofOblInput are declared with the modifier pure.
     */
    public abstract boolean checkPurity();

    public void read(ModStrategy mod) throws ProofInputException{}

    /**
     * The Java Model is already initialized;
     */
    public String readModel() throws ProofInputException{
	return null;
    }
    
    public void initJavaModelSettings(String path) {}

    /** returns the path to the Java model.
     */
    public String getJavaPath(){
	return javaPath;
    }

    /** set the initial configuration used to read an input. It may become
     * modified during reading depending on the modification strategy used
     * for reading.
     */
    public void setInitConfig(InitConfig i){
	initConfig = i;
    }

    /** Specs have already been read.
     */
    public void readSpecs(){
    }

    public void readActivatedChoices() throws ProofInputException{
	//nothing to do
    }

    /** reads the include section and returns an Includes object.  
     */
    public Includes readIncludes() throws ProofInputException{
	return new Includes();
    }
    
    /** returns the name of the proof obligation input.
     */
    public String name(){
	return spec.toString();
    }

    public Contractable[] getObjectOfContract(){
        return new Contractable[] { 
                new JavaModelMethod(pm, javaPath, initConfig.getServices())};
    }

    public void startProtocol() {
	// do nothing
    }

    public String createProgramVarsSection(){
	IteratorOfNamed it = initConfig.progVarNS().allElements().iterator();
	String result = "\\programVariables {\n";
	while(it.hasNext()){
	    final ProgramVariable pv = (ProgramVariable) it.next();
            final Type javaType = pv.getKeYJavaType().getJavaType();
            if (javaType instanceof ArrayType) {
                result += 
                    ((ArrayType)javaType).getAlternativeNameRepresentation()+" "+pv.name()+";\n";
            } else {
                result += javaType.getFullName()+" "+pv.name()+";\n";
            }
	}
	result += "}\n";
	return result;
    }

    public String createFunctionSection(){
	IteratorOfNamed it = spec.getFunctionNS().allElements().iterator();
	String result = "\\functions {\n";
	while(it.hasNext()){
	    Function f = (Function) it.next();
	    result += f.proofToString();
	}
	result += "}\n";
	return result;
    }

    public String createJavaSection(){
	return "\\javaSource \""+getJavaPath()+"\";\n";
    }

    public String createProblemHeader(){
	return createJavaSection()+"\n"+createProgramVarsSection()+"\n"+
	    createFunctionSection()+"\n";
    }
}


