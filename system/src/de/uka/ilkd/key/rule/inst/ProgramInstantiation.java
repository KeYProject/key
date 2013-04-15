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
import de.uka.ilkd.key.logic.op.SchemaVariable;

/** This class is used to store the instantiation of a schemavarible
 * if it is a ProgramElement.
 */
public class ProgramInstantiation extends InstantiationEntry {

    /** the pe the schemavariable is instantiated with */
    private final ProgramElement pe ;

   
    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     */
    ProgramInstantiation(SchemaVariable sv, ProgramElement pe) {
	super(sv);
	this.pe = pe;
    }


    /** returns the ProgramElement the SchemaVariable is instantiated with
     * @return the ProgramElement the SchemaVariable is instantiated with
     */
    public ProgramElement getProgramElement() {
	return pe;
    }

    
    @Override
    public Object getInstantiation() {
	return pe;
    }
    

    @Override
    public String toString() {
	return "[" + getSchemaVariable() + ", " + getProgramElement() + "]";
    }
}
