// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.strategy.FOLStrategy;
import de.uka.ilkd.key.strategy.SetOfStrategyFactory;
import de.uka.ilkd.key.strategy.StrategyFactory;

public class PureFOLProfile extends AbstractProfile {
   
    private final static StrategyFactory DEFAULT = new FOLStrategy.Factory();
    
    public PureFOLProfile() {
        super("standardRules-FOL.key");       
    }

    public String name() {
        return "Pure FOL Profile";
    }

    protected SetOfStrategyFactory getStrategyFactories() {  
        return super.getStrategyFactories().
            add(DEFAULT);
    }  
       
    public StrategyFactory getDefaultStrategyFactory() {        
        return DEFAULT;
    }
}
