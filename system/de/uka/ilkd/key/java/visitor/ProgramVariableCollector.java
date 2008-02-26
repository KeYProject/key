// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;
import java.util.Map;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.EverythingLocationDescriptor;
import de.uka.ilkd.key.logic.IteratorOfLocationDescriptor;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.soundness.TermProgramVariableCollector;
import de.uka.ilkd.key.speclang.LoopInvariant;

/** 
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used collect all ProgramVariables in a program.
 */
public class ProgramVariableCollector extends JavaASTVisitor {

    private final HashSet result = new HashSet();
    private final boolean collectFunctionLocations;

    /**
     * collects all program variables occuring in the AST <tt>root</tt>
     * using this constructor is equivalent to <tt>ProggramVariableCollector(root, false)</tt> 
     * @param root the ProgramElement which is the root of the AST
     * @param services the Services object
     */
    public ProgramVariableCollector(ProgramElement root, 
                                    Services services, 
                                    boolean collectFunctionLocations) {
	super(root, services);
        assert services != null;
        this.collectFunctionLocations = collectFunctionLocations;
    }
    
    public ProgramVariableCollector(ProgramElement root, 
                                    Services services) {
        this(root, services, false);
    }
    
    /** starts the walker*/
    public void start() {	
	walk(root());	
    }

    public HashSet result() { 
	return result;
    }    

    public String toString() {
	return result.toString();
    }

    protected void doDefaultAction(SourceElement x) {
    }

    public void performActionOnProgramVariable(ProgramVariable pv) {
	result.add(pv);
    }
         
    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);        
    }

    public void performActionOnProgramConstant(ProgramConstant x) {       
        performActionOnProgramVariable(x);
    }
    
    public void performActionOnLoopInvariant(LoopInvariant x) {
        TermProgramVariableCollector tpvc = 
            new TermProgramVariableCollector(services, collectFunctionLocations);
        Term selfTerm = x.getInternalSelfTerm();
        Map atPreFunctions = x.getInternalAtPreFunctions();
        
        //invariant
        x.getInvariant(selfTerm, atPreFunctions, services).execPostOrder(tpvc);
        
        //predicates
        SetOfTerm preds = x.getPredicates(selfTerm, atPreFunctions, services);
        for(IteratorOfTerm it = preds.iterator(); it.hasNext(); ) {
            it.next().execPostOrder(tpvc);
        }
        
        //modifies
        SetOfLocationDescriptor mod 
            = x.getModifies(selfTerm, atPreFunctions, services);
        for(IteratorOfLocationDescriptor it = mod.iterator(); it.hasNext(); ) {
            LocationDescriptor loc = it.next();
            if(loc instanceof BasicLocationDescriptor) {
                BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;
                bloc.getFormula().execPostOrder(tpvc);
                bloc.getLocTerm().execPostOrder(tpvc);
            } else {
                assert loc instanceof EverythingLocationDescriptor;
            }
        }
        
        //variant
        Term v = x.getVariant(selfTerm, atPreFunctions, services);
        if(v != null) {
            v.execPostOrder(tpvc);
        }

        result.addAll(tpvc.result());
    }
}
