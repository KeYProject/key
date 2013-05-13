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

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

public interface IBuiltInRuleApp extends RuleApp {

    /**
     * returns the built in rule of this rule application
     */
    BuiltInRule rule();

    /**
     * tries to complete the rule application from the available information
     * Attention: Do neither add GUI code to the rules nor use this method directly 
     * Instead ask the implementation of the {@link de.uka.ilkd.key.ui.UserInterface} to complete a built-in rule
     * For an example implementation see e.g. {@link UseOperationContractRule} or {@link UseDependencyContractRule}.    
     */
    IBuiltInRuleApp tryToInstantiate(Goal goal);

    List<LocationVariable> getHeapContext();

    /**
     * returns true if tryToInstantiate may be able to complete the app
     * @return
     */
    boolean isSufficientlyComplete();
    
    ImmutableList<PosInOccurrence> ifInsts();

    IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts);

    IBuiltInRuleApp replacePos(PosInOccurrence newPos);

}