// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.Operator2;
import de.uka.ilkd.key.logic.sort.Sort;

/** This class represents the function operator,
 * to be able to express properties of function with
 * many arguments.
 * @author Stanislas Nanchen 
 */

public abstract class FunctionOperator extends AsmOp {
    
    public static Operator2 function(final Name id) {
	return new FunctionOperator("function", Sort.FORMULA, new Sort[] {null, Sort.FORMULA}) {
		
		/** the name used for the NArityLogicVariable */
		public Name getVariableName() {
		    return new Name("%" + id.toString());
		}

	    };
    }

    private FunctionOperator(String name, Sort sort, Sort[] args) {
	super(new Name(name), sort, args);
    }

  

    /** the name used for the NArityLogicVariable */
    public Name getVariableName() {
	return new Name("%");
    }

}
