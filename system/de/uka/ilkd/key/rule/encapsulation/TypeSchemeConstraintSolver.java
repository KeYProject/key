// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.encapsulation;


class TypeSchemeConstraintSolver {
    private TypeSchemeConstraint constraint;
    private TypeSchemeVariable vars[];

    
    private boolean run(int varPos) {
        if(varPos >= vars.length) {
            return true;
        }
        
        IteratorOfTypeScheme it = vars[varPos].getValueRange().iterator();
        while(it.hasNext()) {
            vars[varPos].assignValue(it.next());
            if(constraint.evaluate()) {
                if(run(varPos + 1)) {
                    return true;
                }
            }
        }
        
        vars[varPos].assignDefaultValue();
        return false;
    }

    
    /**
     * Tries to solve a type scheme constraint.
     * @param constraint the constraint; after a successful execution of this
     * method, the values assigned to its type scheme variables describe the
     * solution
     * @return true if successful, false otherwise
     */
    public boolean solve(TypeSchemeConstraint constraint) {
        this.constraint = constraint;
        this.vars       = constraint.getFreeVars().toArray();
        
        for(int i = 0; i < vars.length; i++) {
            vars[i].assignDefaultValue();
        }
        
        return run(0) && constraint.evaluate();
    }
}
