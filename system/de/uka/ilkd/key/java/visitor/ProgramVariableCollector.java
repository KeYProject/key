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

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.logic.IteratorOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
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

    private static final TermBuilder TB = TermBuilder.DF;
    private final HashSet result = new HashSet();

    /**
     * collects all program variables occuring in the AST <tt>root</tt>
     * using this constructor is equivalent to <tt>ProggramVariableCollector(root, false)</tt> 
     * @param root the ProgramElement which is the root of the AST
     * @param services the Services object
     */
    public ProgramVariableCollector(ProgramElement root, Services services) {
	super(root, services);
        assert services != null;
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
            new TermProgramVariableCollector(services);
        Term pseudoSelfTerm = x.getSelfVar() == null 
                              ? null 
                              : TB.var(x.getSelfVar());
        x.getInvariant(pseudoSelfTerm).execPostOrder(tpvc);
        IteratorOfTerm it = x.getPredicates(pseudoSelfTerm).iterator();
        while(it.hasNext()) {
            it.next().execPostOrder(tpvc);
        }
        result.addAll(tpvc.result());
    }
}
