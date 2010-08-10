// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.inst;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.logic.op.SchemaVariable;


public class ProgramSkolemInstantiation extends ProgramInstantiation {

    public static final int OCCURRING_VARIABLE    = 0;
    public static final int NEW_BOUND_VARIABLE    = 1;
    public static final int NEW_FREE_VARIABLE     = 2;
    public static final int NEW_NOT_FREE_VARIABLE = 3;
    public static final int NEW_EXPRESSION        = 4;

    private final int instantiationType;

    /** creates a new ContextInstantiationEntry 
     * @param sv the SchemaVariable that is
     * instantiated
     * @param pe the ProgramElement the SchemaVariable is instantiated with
     */
    ProgramSkolemInstantiation( SchemaVariable sv,
			        ProgramElement pe,
				int            instantiationType ) {
	super(sv, pe);
	this.instantiationType = instantiationType;
    }

    public int getInstantiationType() {
	return instantiationType;
    }

}
