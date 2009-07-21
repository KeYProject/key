// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.SetOfLocationDescriptor;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.TermProgramVariableCollector;
import de.uka.ilkd.key.speclang.LoopInvariant;

/** 
 * Walks through a java AST in depth-left-fist-order. 
 * This walker is used collect all LocationVariables and optional function locations.
 */
public class ProgramVariableCollector extends JavaASTVisitor {

    private final HashSet<UpdateableOperator> result = new HashSet<UpdateableOperator>();
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

    public HashSet<UpdateableOperator> result() { 
	return result;
    }    

    public String toString() {
	return result.toString();
    }

    protected void doDefaultAction(SourceElement x) {
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        result.add(x);
    }
    
    public void performActionOnLoopInvariant(LoopInvariant x) {
        TermProgramVariableCollector tpvc = 
            new TermProgramVariableCollector(services);
        Term selfTerm = x.getInternalSelfTerm();
        Map<Operator, Function> atPreFunctions = x.getInternalAtPreFunctions();
        
        //invariant
        Term inv = x.getInvariant(selfTerm, atPreFunctions, services);
        if(inv != null) {
            inv.execPostOrder(tpvc);
        }
        
        //predicates
        SetOfTerm preds = x.getPredicates(selfTerm, atPreFunctions, services);
        for(Term pred : preds) {
            pred.execPostOrder(tpvc);
        }
        
        //modifies
        SetOfLocationDescriptor mod 
            = x.getModifies(selfTerm, atPreFunctions, services);
        for(LocationDescriptor loc : mod) {
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
