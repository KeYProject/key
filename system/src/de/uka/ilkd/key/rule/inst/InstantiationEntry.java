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

import de.uka.ilkd.key.logic.op.SchemaVariable;

/** This is an abstract class that encapsulates a schemavariable and its
 *  instantiation. It is needed because schemavariables can be
 *  instantiated as ProgramElements and as Terms according to their
 *  type. But we have to put the pair (schemavariable,
 *  term/program-element) in one map. Therefore a map from
 *  SchemaVariable to InstantiationEntry is used
 */
public abstract class InstantiationEntry  {

    /** the instantiated SchemaVariable */
    private final SchemaVariable sv;
    
    /** creates a new InstantiationEntry with the given SchemaVariable
     * @param sv the SchemaVariable that is instantiated
     */
    InstantiationEntry(SchemaVariable sv) {
	this.sv = sv; 
    }

    /** returns the instantiation of the SchemaVariable
     * @return  the instantiation of the SchemaVariable
    */
    public abstract Object getInstantiation();

    /** returns the SchemaVariable that is instantiated 
     * @return the SchemaVariable that is instantiated 
     */
    public SchemaVariable getSchemaVariable() {
	return sv;
    }
}
