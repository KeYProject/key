package org.key_project.jmlediting.core.typechecker;

import java.util.HashMap;

import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;

public abstract class TypeCheckerFunctions {
    
    private static HashMap<Integer, ITypeComputeFunction> functions = new HashMap<Integer, ITypeComputeFunction>();
    
    private TypeCheckerFunctions() {}
    
    public ITypeComputeFunction get(final int i) {
        if(functions.containsKey(i)) {
            return functions.get(i);
        } else {
            return null;
        }
    }
    
    
    
}
