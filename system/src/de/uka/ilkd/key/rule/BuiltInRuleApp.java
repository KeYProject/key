// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;

/** 
 * this class represents an application of a built in rule
 * application
 */
public class BuiltInRuleApp extends AbstractBuiltInRuleApp  {
   
    protected BuiltInRuleApp(BuiltInRule builtInRule, 
			  PosInOccurrence pio) {
	this.builtInRule    = builtInRule;
	this.pio            = pio;
    }
    
    
    protected BuiltInRuleApp(BuiltInRule builtInRule, 
			  PosInOccurrence pio,
			  ImmutableList<PosInOccurrence> ifInsts) {
	this(builtInRule, pio);
	this.ifInsts = ifInsts;
    }
    


    @Override
    public RuleApp replacePos(PosInOccurrence newPos) {
	    return new BuiltInRuleApp(builtInRule, newPos, ifInsts);
    }


}
