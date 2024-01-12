/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

/**
 * Interface for creating Strategy instances. The strategy name and the name of the strategy factory
 * are assumed to be the same (you have to refactor if you want to change this).
 */
public interface StrategyFactory extends Named {
    /**
     * Create strategy for a proof.
     *
     * @param proof the Proof a strategy is created for
     * @param strategyProperties the StrategyProperties to customize the strategy
     * @return the newly created strategy
     */
    Strategy create(Proof proof, StrategyProperties strategyProperties);

    /**
     * Returns the {@link StrategySettingsDefinition} which describes how an user interface has to
     * look like to edit {@link StrategySettings} supported by created {@link Strategy} instances.
     *
     * @return The {@link StrategySettingsDefinition} which describes the user interface.
     */
    StrategySettingsDefinition getSettingsDefinition();
}
