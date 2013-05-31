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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.op.SchemaVariable;
/** This class is used to store the instantiation of a schemavariable
 * if it is a ProgramElement.
 */

public class ProgramListInstantiation extends InstantiationEntry {

    /** the pe the schemavariable is instantiated with */
    private final ImmutableArray<ProgramElement> pes ;

   
    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param pes the ProgramElement array the 
     * SchemaVariable is instantiated with
     */
    ProgramListInstantiation(SchemaVariable sv, 
            ImmutableArray<ProgramElement> pes) {
	super(sv);
	this.pes = pes;
    }

    /** returns the ProgramElement the SchemaVariable is instantiated with
     * @return the ProgramElement the SchemaVariable is instantiated with
     */
    public ImmutableArray<ProgramElement> getProgramElements() {
	return pes;
    }
    
    /** returns the intantiation of the SchemaVariable 
     * @return  the intantiation of the SchemaVariable 
     */
    public Object getInstantiation() {
	return pes;
    }

    /** toString */
    public String toString() {
	return "["+getSchemaVariable()+", "+getProgramElements()+"]";
    }

}
