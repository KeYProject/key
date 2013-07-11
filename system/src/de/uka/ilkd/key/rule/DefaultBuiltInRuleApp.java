// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

/**
 * this class represents an application of a built in rule
 * application
 */
public class DefaultBuiltInRuleApp extends AbstractBuiltInRuleApp  {

   public DefaultBuiltInRuleApp(BuiltInRule builtInRule,
			  PosInOccurrence pio) {
        super(builtInRule, pio);
    }


    public DefaultBuiltInRuleApp(BuiltInRule builtInRule,
			  PosInOccurrence pio,
			  ImmutableList<PosInOccurrence> ifInsts) {
        super(builtInRule, pio, ifInsts);
    }

    @Override
    public DefaultBuiltInRuleApp replacePos(PosInOccurrence newPos) {
	    return new DefaultBuiltInRuleApp(builtInRule, newPos, ifInsts);
    }

    @Override
    public DefaultBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }

    @Override
    public DefaultBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
        //return new DefaultBuiltInRuleApp(builtInRule, pio, ifInsts);
    }

}
