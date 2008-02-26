// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.visitor.JavaASTVisitor;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ObjectSort;


class FreeProgramVariableDetector extends JavaASTVisitor {
    private SetOfProgramVariable freeVars;
    private SetOfProgramVariable declaredVars;
    
    
    public FreeProgramVariableDetector(ProgramElement root, Services services) {
        super(root, services);
    }
    
    
    protected void doDefaultAction(SourceElement node) {
    }
    
    
    private boolean isLocalReferenceVar(ProgramVariable pv) {
        return !pv.isMember() && pv.sort() instanceof ObjectSort;
    }
    
    
    public boolean findFreePV() {
        freeVars     = SetAsListOfProgramVariable.EMPTY_SET;
        declaredVars = SetAsListOfProgramVariable.EMPTY_SET;
        walk(root());
        return freeVars.size() > 0;
    }
    
    
    public void performActionOnProgramVariable(ProgramVariable pv) {
        if(isLocalReferenceVar(pv) && !declaredVars.contains(pv)) {
            freeVars = freeVars.add(pv);
        }
    }
    
    
    public void performActionOnVariableSpecification(VariableSpecification vs) {
        ProgramVariable pv = (ProgramVariable) vs.getProgramVariable();
        if(isLocalReferenceVar(pv)) {
            freeVars     = freeVars.remove(pv);
            declaredVars = declaredVars.add(pv);
        }
    }


    public void performActionOnLocationVariable(LocationVariable x) {
        performActionOnProgramVariable(x);
    }


    public void performActionOnProgramConstant(ProgramConstant x) {      
        performActionOnProgramVariable(x);
    }
}
