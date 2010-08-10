// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang.ocl.translation;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.util.Debug;


class OCLParameters extends SLParameters {
    private final ImmutableList<LogicVariable> declaredVars;
    private final ImmutableList<OCLExpression> entities;
            
    public OCLParameters(ImmutableList<LogicVariable> declaredVars,
                         ImmutableList<OCLExpression> entities) {
        super(convertToListOfSLExpression(entities));
        Debug.assertTrue(declaredVars != null);
        Debug.assertTrue(entities != null);
        this.declaredVars = declaredVars;
        this.entities        = entities;
    }
    
    
    private static ImmutableList<SLExpression> convertToListOfSLExpression(ImmutableList<OCLExpression> list) {
        ImmutableList<SLExpression> result = ImmutableSLList.<SLExpression>nil();

        for (OCLExpression aList : list) {
            result = result.append(aList);
        }
        
        return result;
    }


    public ImmutableList<OCLExpression> getEntities() {
        return entities;
    }
        
    
    public ImmutableList<LogicVariable> getDeclaredVars() {
        return declaredVars;
    }
    
    
    public String toString() {
        String result = "(";

        for (LogicVariable declaredVar : declaredVars) {
            result += declaredVar + ",";
        }
        if(!declaredVars.isEmpty()) {
            result = result.substring(0, result.length() - 1) + "|";
        }

        for (OCLExpression entity : entities) {
            result += entity + ",";
        }
        if(!entities.isEmpty()) {
            result = result.substring(0, result.length() - 1);
        }
        
        return result + ")";
    }
}
