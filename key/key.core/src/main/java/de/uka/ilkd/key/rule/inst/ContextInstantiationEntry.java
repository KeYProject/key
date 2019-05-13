// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.PosInProgram;

/** This class is used to store the information about a matched
 * context of a dl formula. (the pi and omega part)
 * TODO: Check if there is a need for ContextStatementBlockInstantiation or if it could be
 * unified with this class
 */
public class ContextInstantiationEntry extends InstantiationEntry<ContextStatementBlockInstantiation> {

    /** 
     * creates a new ContextInstantiationEntry 
     * @param pi the PosInProgram describing the position
     * of the first statement after the prefix
     * @param omega the PosInProgram describing the position
     * of the statement just before the suffix starts
     * @param activeStatementContext the ExecutionContext of the first
     * active statement
     * @param pe the ProgramElement the context positions are related to
     */
    ContextInstantiationEntry(PosInProgram pi,
			      PosInProgram omega, 
			      ExecutionContext activeStatementContext,
			      ProgramElement pe) {
	super(new ContextStatementBlockInstantiation
	        (pi, omega, activeStatementContext, pe));
    }

    /** returns the position of the first statement after the prefix
     * @return the position of the first statement after the prefix
     */
    public PosInProgram prefix() {
	return getInstantiation().prefix();
    }


    /** returns the position of the statement just before the suffix
     * starts  
     * @return the position of the statement just before the suffix
     * starts 
     */
    public PosInProgram suffix() {
	return getInstantiation().suffix();
    }

    /** 
     * returns the context program with an ignorable part between prefix
     * and suffix position
     */
    public ProgramElement contextProgram() {
	return getInstantiation().programElement();
    }

    /** 
     * returns the execution context of the first active statement or
     * null if match is performed outer most
     */
    public ExecutionContext activeStatementContext() {
	return getInstantiation().activeStatementContext();
    }

    /** toString */
    public String toString() {
	return "[\npi:"+prefix()+"\nomega:"+suffix()+"\n]";
    }

}