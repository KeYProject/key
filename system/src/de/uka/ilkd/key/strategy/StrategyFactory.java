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

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.proof.Proof;
/**
 * Interface for creating Strategy instances.
 * The strategy name and the name of the strategy factory are assumed to be the same
 *  (you have to refactor if you want to change this).
 */
public abstract class StrategyFactory implements Named {
    
    /**
     * Create the strategy with the specified name.
     * If there is no strategy with the specified name, this method behaves as
     * if the name of the default strategy was given.
     * @param proof the proof for which the strategy is to be created
     * @param name the name of the strategy
     * @return the strategy
     */
    
    public static Strategy create ( Proof proof, String name,
                                    StrategyProperties strategyProperties ) {
     
        StrategyFactory createdFactory = null;
        try {
            createdFactory = (StrategyFactory) Class.forName(
                    "de.uka.ilkd.key.strategy."+name+"$Factory").newInstance();
        } catch (ClassNotFoundException e) {
            throw new RuntimeException(e);
        } catch (InstantiationException e) {
            throw new RuntimeException(e);
        } catch (IllegalAccessException e) {
            throw new RuntimeException(e);
        } 
        
        return createdFactory.create ( proof , strategyProperties );
    }
    
    /**
     * Create strategy for a proof.
     * @param proof the Proof a strategy is created for 
     * @param strategyProperties the StrategyProperties to customize the 
     * strategy
     * @return the newly created strategy
     */
    public abstract Strategy create(Proof proof, 
            StrategyProperties strategyProperties);
    
}
