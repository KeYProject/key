// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * variable condition used if a new variable is introduced
 */
public class NewVarcond {

    private SchemaVariable sv;
    private SchemaVariable asSort = null;
    private Sort sort = null;
    private boolean elementsort=false;

    public NewVarcond(SchemaVariable sv, SchemaVariable asSort) {
	this.sv=sv;
	this.asSort=asSort;
    }
    
    /*
     * @param sv the Schemavariable representing a new variable.
     * @param asSort a Schemavariable defining the sort of the new variable.
     * @param es true if asSort is an ArraySV and the sort of sv should be 
     * the same as the elementsort of asSort. false otherwise. 
     */
    public NewVarcond(SchemaVariable sv, SchemaVariable asSort, boolean es) {
	this.sv=sv;
	this.asSort=asSort;
	elementsort = es;
    }

    public NewVarcond(SchemaVariable sv, Sort sort) {
	this.sv=sv;
	this.sort=sort;
    }

    public boolean isDefinedByType() {
	return asSort==null;
    }

    public SchemaVariable getSchemaVariable() {
	return sv;
    }

    public SchemaVariable getPeerSchemaVariable() {
	return asSort;
    }

    public Sort getSort() {
	return sort;
    }
    
    public boolean isDefinedByElementSort(){
        return elementsort;
    }

    public Object getSortDefiningObject() {
	return isDefinedByType() ? getSort() : getPeerSchemaVariable();
    }

    public String toString() {
	return "\\new("+sv+", "+ (isDefinedByType() ? ""+sort : (isDefinedByElementSort()? 
	  "\\elemTypeof(" : "\\typeof(")+getPeerSchemaVariable()+")")+")";
    }

}
