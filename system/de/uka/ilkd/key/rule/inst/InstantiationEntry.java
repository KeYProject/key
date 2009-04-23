// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.logic.op.SchemaVariable;

/** This is an abstract clas that encapsulates a schemvariable and its
 *  instantiation. It is needed because schemavariables can be
 *  instantiated as ProgramElements and as Terms accroding to their
 *  type. But we have to put the pair (schemavariable,
 *  term/programelment) in one map. Therefore a map from
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

    /** returns the intantiation of the SchemaVariable 
     * @return  the intantiation of the SchemaVariable 
    */
    public abstract Object getInstantiation();

    /** returns the SchemaVariable that is instantiated 
     * @return the SchemaVariable that is instantiated 
     */
    public SchemaVariable getSchemaVariable() {
	return sv;
    }
}
