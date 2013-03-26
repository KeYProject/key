// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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
import de.uka.ilkd.key.logic.op.SchemaVariable;

/** This class is used to store the information about a matched
 * context of a dl formula. (the pi and omega part)
 */

public class ContextInstantiationEntry extends InstantiationEntry {

    /** the prefix and suffix instantiation */
    private ContextStatementBlockInstantiation inst;
       
    /** 
     * creates a new ContextInstantiationEntry 
     * @param ctxt the SchemaVariable that is
     * instantiated
     * @param pi the PosInProgram describing the position
     * of the first statement after the prefix
     * @param omega the PosInProgram describing the position
     * of the statement just before the suffix starts
     * @param activeStatementContext the ExecutionContext of the first
     * active statement
     * @param pe the ProgramElement the context positions are related to
     */
    ContextInstantiationEntry(SchemaVariable ctxt, 
			      PosInProgram pi,
			      PosInProgram omega, 
			      ExecutionContext activeStatementContext,
			      ProgramElement pe) {
	super(ctxt);
	inst = new ContextStatementBlockInstantiation
	    (pi, omega, activeStatementContext, pe);
    }

    /** returns the position of the first statement after the prefix
     * @return the position of the first statement after the prefix
     */
    public PosInProgram prefix() {
	return inst.prefix();
    }


    /** returns the position of the statement just before the suffix
     * starts  
     * @return the position of the statement just before the suffix
     * starts 
     */
    public PosInProgram suffix() {
	return inst.suffix();
    }

    /** 
     * returns the context program with an ignorable part between prefix
     * and suffix position
     */
    public ProgramElement contextProgram() {
	return inst.programElement();
    }

    /** 
     * returns the execution context of the first active statement or
     * null if match is performed outer most
     */
    public ExecutionContext activeStatementContext() {
	return inst.activeStatementContext();
    }


    /** returns the instantiation of the SchemaVariable 
     * @return  the instantiation of the SchemaVariable 
    */
    public Object getInstantiation() {
	return inst;
    }

    /** toString */
    public String toString() {
	return "["+getSchemaVariable()+",\npi:"+prefix()+"\nomega:"+suffix()+"\n]";
    }

}
