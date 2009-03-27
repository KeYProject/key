// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * represents an update pair (lhs, rhs) with a guard and quantified 
 * variables <code>v1,...,vn</code>, which would be written as
 *  <code>\for v1,...,vn \if guard lhs := rhs</code>
 */
public class UpdatePairWithGuard {
    private Term lhs;
    private Term rhs;
    Term guard;
    private QuantifiableVariable[] qvars;
    
    
    public UpdatePairWithGuard(Term lhs, Term rhs, 
                               Term guard, QuantifiableVariable[] qvars) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.guard = guard;
        this.qvars = qvars;
    }
    
    public Term getLHS() {
        return lhs;
    }

    public Term getRHS() {
        return rhs;
    }

    public Term getGuard() {
        return guard;
    }

    public QuantifiableVariable[] getQuantifiedVars() {
        return qvars;
    }
    
    public ArrayOfQuantifiableVariable createArrayOfQuantifiedVars() {
        return new ArrayOfQuantifiableVariable(qvars);
    }
}
