// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.AbstractUseOperationContractRule;
import de.uka.ilkd.key.rule.Rule;

public class UseOperationContractRuleFilter implements RuleFilter {

    public static final RuleFilter INSTANCE = new UseOperationContractRuleFilter ();
    
    private UseOperationContractRuleFilter () {
    }
    
    public boolean filter(Rule rule) {        
        return (rule instanceof AbstractUseOperationContractRule);
    }

}
