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


package de.uka.ilkd.key.proof.mgt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.RuleApp;

public interface ComplexRuleJustification extends RuleJustification {
    
    public RuleJustification getSpecificJustification(RuleApp app, 
                                                      Services services);
    
}
