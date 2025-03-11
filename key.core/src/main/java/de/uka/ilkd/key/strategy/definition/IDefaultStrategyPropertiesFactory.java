/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.definition;

import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyProperties;

/**
 * Instances of this factory are used to create default {@link StrategyProperties} used by a
 * {@link Strategy} defined via its {@link StrategySettingsDefinition}.
 *
 * @author Martin Hentschel
 */
public interface IDefaultStrategyPropertiesFactory {
    /**
     * The default implementation.
     */
    IDefaultStrategyPropertiesFactory DEFAULT_FACTORY =
        StrategyProperties::new;

    /**
     * Creates new default {@link StrategyProperties}.
     *
     * @return The new default {@link StrategyProperties}.
     */
    StrategyProperties createDefaultStrategyProperties();
}
