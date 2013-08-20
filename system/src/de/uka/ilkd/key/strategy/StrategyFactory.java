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

import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
/**
 * Interface for creating Strategy instances.
 * The strategy name and the name of the strategy factory are assumed to be the same
 *  (you have to refactor if you want to change this).
 */
public interface StrategyFactory extends Named {
    /**
     * Create strategy for a proof.
     * @param proof the Proof a strategy is created for 
     * @param strategyProperties the StrategyProperties to customize the 
     * strategy
     * @return the newly created strategy
     */
    public Strategy create(Proof proof, StrategyProperties strategyProperties);
    
    /**
     * Returns the {@link StrategySettingsDefinition} which describes
     * how an user interface has to look like to edit {@link StrategySettings}
     * supported by created {@link Strategy} instances.
     * @return The {@link StrategySettingsDefinition} which describes the user interface.
     */
    public StrategySettingsDefinition getSettingsDefinition();
}
