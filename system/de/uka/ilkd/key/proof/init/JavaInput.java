// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.logic.SetAsListOfChoice;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.util.ProgressMonitor;


/**
 * This is the input type for JML enriched java source files or such
 * source files in a directory tree structure
 * @deprecated
 */
public class JavaInput extends KeYUserProblemFile implements ProofOblInput {

    File path = null;
    
    /**
     * @param name
     * @param path
     * @param monitor
     */
    public JavaInput(String name, File path, ProgressMonitor monitor) {
	super(name, path, monitor);
	this.path = path;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.ProofOblInput#getPO()
     */
    public ProofAggregate getPO() {
        
        Term dummy = TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);
        
        
        
        // create empty dummy proof to ensure the java model was loaded
        return ProofAggregate.createProofAggregate(
                new Proof("dummy proof", dummy, "", 
                        getInitConfig().createTacletIndex(),
                        getInitConfig().createBuiltInRuleIndex(),
                        getInitConfig().getServices()),
                "dummy proof");
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.EnvInput#getNumberOfChars()
     */
    public int getNumberOfChars() {
	return 0;
    }

    /** starts reading the input and modifies the InitConfig of this 
     * object with respect to the given modification strategy.
     * @param mod	the modification strategy to use 
     */
    public void read(ModStrategy mod) throws ProofInputException{
	return;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#readProblem(de.uka.ilkd.key.proof.init.ModStrategy)
     */
    public void readProblem(ModStrategy mod) throws ProofInputException{
	return;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.ProofOblInput#askUserForEnvironment()
     */
    public boolean askUserForEnvironment(){
	return false;
    }
    
    /** returns the path to the Java model.
     */
    public String readJavaPath() throws ProofInputException{
        String javaPath = null;
        try{
            javaPath = path.getCanonicalFile().getAbsolutePath();
        } catch(IOException ioe) {
	    throw new ProofInputException(ioe);
        }
        return javaPath;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#readActivatedChoices()
     */
    public void readActivatedChoices() throws ProofInputException{
	initConfig.setActivatedChoices(SetAsListOfChoice.EMPTY_SET);
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#readIncludes()
     */
    public Includes readIncludes() throws ProofInputException{
	return new Includes();
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#getObjectOfContract()
     */
    public Contractable[] getObjectOfContract(){
        return new Contractable[0];
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#initContract(de.uka.ilkd.key.proof.mgt.Contract)
     */
    public boolean initContract(Contract ct){
        return false;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#readFuncAndPred(de.uka.ilkd.key.proof.init.ModStrategy)
     */
    public void readFuncAndPred(ModStrategy mod) throws ProofInputException {
	return;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#readSorts(de.uka.ilkd.key.proof.init.ModStrategy)
     */
    public void readSorts(ModStrategy mod) throws ProofInputException {
	return;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#readRulesAndProblem(de.uka.ilkd.key.proof.init.ModStrategy)
     */
    public void readRulesAndProblem(ModStrategy mod) throws ProofInputException{
	return;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.init.KeYFile#readProof(de.uka.ilkd.key.proof.ProblemLoader)
     */
    public void readProof(ProblemLoader prl) throws ProofInputException {
	return;
    }
}
