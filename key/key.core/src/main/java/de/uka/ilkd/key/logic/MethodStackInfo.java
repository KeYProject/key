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

package de.uka.ilkd.key.logic;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.op.IProgramMethod;

public class MethodStackInfo implements NameCreationInfo {

    public static NameCreationInfo create(ProgramElement program) {
        return new MethodStackInfo(program);
    }

    private final ProgramElement element;
    
        
    public MethodStackInfo(ProgramElement element) {
        this.element = element;
    }
    
    /**
     * returns the method call stack 
     */
    public ImmutableList<IProgramMethod> getMethodStack() {
        ImmutableList<IProgramMethod> list = ImmutableSLList.<IProgramMethod>nil();        
        if (element instanceof ProgramPrefix) {
            final ImmutableArray<ProgramPrefix> prefix = ((ProgramPrefix) element).getPrefixElements(); 
            for (int i = prefix.size() - 1; i>=0; i--) {
                if(prefix.get(i) instanceof MethodFrame) {
                    final MethodFrame frame = (MethodFrame)prefix.get(i);
                    IProgramMethod method = frame.getProgramMethod();
                    if(method != null) {
                        list = list.prepend(method);
                    }
                }
            }
        }
        return list;
    }

    
    public String infoAsString() {
        String result = "Method stack:\n";

        for (IProgramMethod method : getMethodStack()) {
            result += "- " + method.getProgramElementName().toString() + "\n";
        }

	if(result.length() < 1) return "";

        result = result.substring(0, result.length() - 1);

        return result;
    }



}