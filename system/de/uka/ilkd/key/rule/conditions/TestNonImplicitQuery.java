// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TestNonImplicitQuery extends VariableConditionAdapter {

    private SchemaVariable sv;

    public TestNonImplicitQuery(SchemaVariable sv) {
	this.sv = sv;
    }

    public SchemaVariable schemaVariable() {
	return sv;
    }

    public boolean check(SchemaVariable var, SVSubstitute methodName, 
			 SVInstantiations matchCond, 
			 Services services) {
	if (var != schemaVariable()) {
	    return true;  // not responsible
	}
	return !methodName.toString().startsWith("<");
    }

    public String toString() {
	return "\\isNonImplicitQuery(" +schemaVariable()+ ")";
    }

    public boolean equals(Object o) {
	if (!(o instanceof TestNonImplicitQuery)) {
	    return false;
	}
	TestNonImplicitQuery tq = (TestNonImplicitQuery) o;
	return (tq.schemaVariable() == schemaVariable());
    }
    
    public int hashCode(){
    	int result = 5;
    	result = 37 * result + schemaVariable().hashCode();
    	return result;
    }

}
