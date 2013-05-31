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



package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.rule.RuleApp;

/**
 * Interface for collecting <code>RuleApp</code>s, together with their
 * assigned cost. This interface is used in the signature of the
 * method <code>Strategy.instantiateApp</code>
 */
public interface RuleAppCostCollector {
    void collect(RuleApp app, RuleAppCost cost);
}
