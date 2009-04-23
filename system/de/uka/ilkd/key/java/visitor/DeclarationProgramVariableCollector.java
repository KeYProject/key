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
import java.util.Set;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.ImplicitFieldSpecification;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;

/** 
 * The DeclarationProgramVariableCollector collects all top level
 * declared program variables relative to the given block to be
 * visited, for example starting with <code>
 *  { int j; { int i; } { int h; } for (int k; ...) {} int h; }
 * </code>
 *  the collector will return a set containg <code>j, h</code> the
 *  <code>h</code> because of the second occurrence of <code>h</code>
 */
public class DeclarationProgramVariableCollector extends JavaASTVisitor {

    private Set result = new HashSet();


    /** creates a new declaration visitor */
    public DeclarationProgramVariableCollector(ProgramElement root, 
                                               Services services) {
	super(root, services);
    }
    
    /** starts the walker*/
    public void start() {	
	walk(root());	
    }

    public Set result() { 
	return result;
    }    

    public String toString() {
	return result.toString();
    }
    
    /**
     * adds the given variable if we are currently at top level
     */
    protected void addVariable(IProgramVariable var) {
	if (depth() == 1) {
	    result.add(var);
	}
    }

    protected void doDefaultAction(SourceElement x) {
    }

    public void performActionOnVariableSpecification(VariableSpecification x) {
	addVariable(x.getProgramVariable());
    }
 
    public void performActionOnFieldSpecification(FieldSpecification x) {
	addVariable(x.getProgramVariable());
    }

    public void performActionOnImplicitFieldSpecification(ImplicitFieldSpecification x) {
	addVariable(x.getProgramVariable());
    }

    public void performActionOnCatchAllStatement(CatchAllStatement x) {
	result.add(x.getParameterDeclaration().getVariableSpecification()
		   .getProgramVariable());
    }

    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
        
    }

    public void performActionOnProgramConstant(ProgramConstant x) {
        performActionOnProgramVariable(x);
    }
    
}
