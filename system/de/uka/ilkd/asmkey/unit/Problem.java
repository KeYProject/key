// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

import de.uka.ilkd.key.logic.SetAsListOfChoice;
import de.uka.ilkd.key.logic.SetOfChoice;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;

/** This class represent a problem (prop/taclet) that 
 * has to be proved. As such, it implements the
 * {@link ProofOblInput} interface to serve as input
 * for the prover.
 */
public abstract class Problem implements ProofOblInput {

    protected InitConfig initConfig;
    private Unit unit;

    public Problem(Unit unit) {
	this.unit = unit;
    }

    /** 
     * @returns the unit where the problem is.
     */
    public Unit unit() {
	return unit;
    }

    /* --- implementation of {@link ProofOblInput} --- */

    /** returns the proof obligation term as result of the proof obligation
     * input. If there is still no input available because nothing has
     * been read yet null is returned.
     */
    public abstract ProofAggregate getPO();

    /** starts reading the input and modifies the InitConfig of this 
     * object with respect to the given modification
     * strategy. 
     */
    public void read(ModStrategy mod) throws ProofInputException {
	// we have nothing to read, everything is already loaded.
    }

    public void readProblem(ModStrategy mod) throws ProofInputException {
	// we have nothing to read, everything is already loaded.
    }

    public boolean askUserForEnvironment() {
	return true;
    }


    /** returns the path to the Java model.
     */
    public String getJavaPath() throws ProofInputException {
	throw new ProofInputException("AsmKey:unit.Problem: there is no java model in AsmKey.");
    }

    /** set the initial configuration used to read an input. It may become
     * modified during reading depending on the modification strategy used
     * for reading.
     */
    public void setInitConfig(InitConfig i) {
	this.initConfig = i;
    }

    public void readSpecs() {
	// we do nothing. no specs for asmkey.
    }

    public void readActivatedChoices() throws ProofInputException {
	//no choices
    }
    
    /** reads the include section and returns an Includes object.  
     */
    public Includes readIncludes() throws ProofInputException {
	throw new ProofInputException("AsmKeY: Includes not yet implemented.");
    }
    
    /** returns the name of the proof obligation input.
     */
    public abstract String name();

    public Contractable[] getObjectOfContract() {
	return new Contractable[0];
    }

    public boolean initContract(Contract ct) {
	return false;
    }

    public void startProtocol() {
	// do nothing
    }
}
