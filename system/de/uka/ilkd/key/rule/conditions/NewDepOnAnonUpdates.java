// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.VariableCondition;


public class NewDepOnAnonUpdates implements VariableCondition {
    
    private final SchemaVariable modifiesSV, updateSV;

    
    public NewDepOnAnonUpdates(SchemaVariable update, SchemaVariable modifies){
        this.modifiesSV= modifies;
        this.updateSV = update;
        assert updateSV.isFormulaSV () : "newDependingOnMod: First argument has to be a formulaSV";
        assert modifies.isListSV () : "newDependingOnMod: Second argument has to be a listSV";
    }
    

    public MatchConditions check(SchemaVariable var, SVSubstitute instCandidate,
				 MatchConditions matchCond, 
				 Services services) {

        return matchCond;
    }


    public String toString(){
        return "\\new(" + updateSV + ", \\dependingOnMod(" + modifiesSV + ")";
    }

    
    public SchemaVariable getModifiesSV() {
        return modifiesSV;
    }

    public SchemaVariable getUpdateSV() {
        return updateSV;
    }
}
