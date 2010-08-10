// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2008 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigidFunctionLocation;

/**
 * Class is needed to be able to distinguish NonRigidFunctionLocations while
 * working on TestGeneration
 * 
 * @author mbender
 * 
 */
public class NRFLIdentifier {
   // private final Name name;

   // private final int arity;
    
    private final Term t;

    /**In the original implementation the constructor took an Operator as argument. Thus
     * value(a) could not be distinguished from value(b) as the operator in both cases was "value".
     * This lead to overlapping hashkeys for different locations and finally to overwriting of
     * an assignment like value(a)=1 by value(b)=3. But what was the reason for the 
     * original implementation? I'm not sure if the current solution is correct.*/
    public NRFLIdentifier(Term t) {
	if(! (t.op() instanceof NonRigidFunctionLocation))throw new RuntimeException("Type mismatch:"+t.op()+" is not a NonRigidFunctionLocation");
//        this.name = t.op().name();
//        this.arity = t.op().arity();
        this.t=t;
    }

    public boolean equals(Object o) {
	return t.equals(o);
//        if (o instanceof NRFLIdentifier) {
//            return ((NRFLIdentifier) o).arity == arity
//                    && ((NRFLIdentifier) o).name.toString().equals(
//                            name.toString());
//        } else {
//            return false;
//        }
    }

    public String toString() {
	return t.toString();
        //return arity + ", " + name;
    }

    public int hashCode() {
	return t.hashCode();
        //return name.hashCode() * 17 + arity * 17 * 17;
    }
}
