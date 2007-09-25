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
import de.uka.ilkd.key.logic.op.LogicVariable;
//import de.uka.ilkd.asmkey.logic.CollectionSort;

/** This class is used with the big operators. It is
 * used to generate either:
 * - n variables in the quantifier.
 * - a function call with these n variables as argument in
 *   the formula of a big operator.
 *
 * - its sorts is the universal one. i.e. it always match correctly
 *   as the real sorts will be checked after expansion.
 *
 * @author Stanislas Nanchen 
 */


public class NArityLogicVariable extends LogicVariable {

    NArityFunction function;

    public NArityLogicVariable(Name name, NArityFunction function) {
	super(name, function.nAritySort());
	this.function = function;
    }
    
    /** @return arity of the Variable as int */
    public int arity() {
	return 0;
    }

    /** @return the name of the function attached to this NArityLogicVariable */
    public NArityFunction function() {
	return function;
    }
    
    /** for debug only */
    public String toString() {
	return "[NArityLogicVariable:name="+name()+",func="+function() +"]";
    }

}
