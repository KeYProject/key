// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.speclang.LoopInvariant;

/** 
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used collect all LocationVariables and optional function locations.
 */
public final class ProgramVariableCollector extends JavaASTVisitor {

    private final HashSet<LocationVariable> result 
    	= new HashSet<LocationVariable>();

    /**
     * collects all program variables occuring in the AST <tt>root</tt>
     * using this constructor is equivalent to <tt>ProggramVariableCollector(root, false)</tt> 
     * @param root the ProgramElement which is the root of the AST
     * @param services the Services object
     */
    public ProgramVariableCollector(ProgramElement root, 
                                    Services services) {
	super(root, services);
        assert services != null;
        result.add(services.getTypeConverter().getHeapLDT().getHeap());
        result.add(services.getTypeConverter().getHeapLDT().getSavedHeap());
    }
    
    
    @Override
    public void start() {	
	walk(root());	
    }

    
    public HashSet<LocationVariable> result() { 
	return result;
    }    

    @Override
    public String toString() {
	return result.toString();
    }

    @Override
    protected void doDefaultAction(SourceElement x) {
    }


    @Override
    public void performActionOnLocationVariable(LocationVariable x) {
        result.add(x);
    }
    
    
    @Override
    public void performActionOnLoopInvariant(LoopInvariant x) {
        TermProgramVariableCollector tpvc = 
            new TermProgramVariableCollector(services);
        Term selfTerm = x.getInternalSelfTerm();
        Term heapAtPre = x.getInternalHeapAtPre();
        
        //invariant
        Term inv = x.getInvariant(selfTerm, heapAtPre, services);
        if(inv != null) {
            inv.execPostOrder(tpvc);
        }
                
        //modifies
        Term mod = x.getModifies(selfTerm, heapAtPre, services);
        if(mod != null) {
            mod.execPostOrder(tpvc);
        }
        
        //variant
        Term v = x.getVariant(selfTerm, heapAtPre, services);
        if(v != null) {
            v.execPostOrder(tpvc);
        }

        result.addAll(tpvc.result());
    }
}
