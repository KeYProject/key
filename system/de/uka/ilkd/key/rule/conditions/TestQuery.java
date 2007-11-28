// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TestQuery extends VariableConditionAdapter {

    private SchemaVariable sv;

    public TestQuery(SchemaVariable sv) {
	this.sv = sv;
    }

    public SchemaVariable schemaVariable() {
	return sv;
    }

    public boolean check(SchemaVariable var, SVSubstitute instCandidate, 
			 SVInstantiations instMap, 
			 Services services) {
	if (var != schemaVariable()) {
	    return true;  // not responsible
	}
	if (!(instCandidate instanceof Term)) {
	    return false;
	}
	return checkTerm((Term) instCandidate);
    }

    private boolean checkTerm(Term t){
	return t.op() instanceof ProgramMethod;
    }

    public String toString() {
	return "\\isQuery(" +schemaVariable()+ ")";
    }

    public boolean equals(Object o) {
	if (!(o instanceof TestQuery)) {
	    return false;
	}
	TestQuery tq = (TestQuery) o;
	return (tq.schemaVariable() == schemaVariable());
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result + schemaVariable().hashCode();
    	return result;
    }

}
