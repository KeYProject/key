// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.proof;

import de.uka.ilkd.asmkey.unit.Unit;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletIndex;

/** In AsmKeY, we need more information with the proof. */
public class AsmProof extends Proof {

    private Unit unit;
    private NonRigidFunction[] dynamics;

    public AsmProof(String name,
		    Term problem,
		    String header,
		    TacletIndex rules,
		    BuiltInRuleIndex builtInRules,
		    Services services,
		    Unit unit) {
	super(name, problem, header, rules, builtInRules, services);
	this.unit = unit;
	this.dynamics = unit.getNonRigidFunctions().toArray();
    }

    public Unit unit() {
	return unit;
    }

    public NonRigidFunction[] getNonRigidFunctions() {
	return dynamics;
    }

}
