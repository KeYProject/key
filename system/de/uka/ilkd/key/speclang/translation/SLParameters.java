// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.speclang.translation;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

public class SLParameters {

    
    private final ImmutableList<SLExpression> parameters;

    public SLParameters(ImmutableList<SLExpression> parameters) {
        this.parameters = parameters;
    }
    
    public ImmutableList<SLExpression> getParameters() {
        return parameters;
    }
    
    
    public boolean isListOfTerm() {

        for (SLExpression parameter : parameters) {
            if (!parameter.isTerm())
                return false;
        }
        
        return true;
    }
    
    public ImmutableList<KeYJavaType> getSignature(Services services) {
            
        ImmutableList<KeYJavaType> result = ImmutableSLList.<KeYJavaType>nil();

        for (SLExpression parameter : parameters) {
            result = result.append(parameter.getKeYJavaType(services.getJavaInfo()));
        }
        
        return result;
    }
        

}
