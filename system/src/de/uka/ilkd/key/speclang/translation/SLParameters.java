// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.TermServices;

/**
 * Wraps a list of expressions.
 */
public final class SLParameters {
    
    private final ImmutableList<SLExpression> parameters;

    public SLParameters(ImmutableList<SLExpression> parameters) {
        this.parameters = parameters;
    }
    
    
    public ImmutableList<SLExpression> getParameters() {
        return parameters;
    }
    
    
    public boolean isListOfTerm() {
	for(SLExpression expr : parameters) {
            if(!expr.isTerm()) {
                return false;
            }
        }
        return true;
    }
    
    
    public ImmutableList<KeYJavaType> getSignature(TermServices services) {           
        ImmutableList<KeYJavaType> result = ImmutableSLList.<KeYJavaType>nil();
        for(SLExpression expr : parameters) {
            result = result.append(expr.getType());
        }        
        return result;
    }

    public String toString() {
        return parameters == null ? "" : parameters.toString();
    }


}