// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** this class contains a Taclet together with its suggested
 * instantiations. */
package de.uka.ilkd.key.rule.inst;


import de.uka.ilkd.key.logic.op.MapFromSchemaVariableToTerm;
import de.uka.ilkd.key.rule.Taclet;
public class TacletInstantiations {

    /** the rule */
    private Taclet rule;
    /** the instantations */
    private MapFromSchemaVariableToTerm instantiations;

    public TacletInstantiations(Taclet rule,
			      MapFromSchemaVariableToTerm instantiations) 
    {
	this.rule=rule;
	this.instantiations=instantiations;
    }

    public Taclet taclet() {
	return rule;
    }

    public MapFromSchemaVariableToTerm instantiations()
    {
	return instantiations;
    }

    public String toString() {
	return "rule: "+taclet()+ "; instantiation: "+instantiations();
    }

    
}
