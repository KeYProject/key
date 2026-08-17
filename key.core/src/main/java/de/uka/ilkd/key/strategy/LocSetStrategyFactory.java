/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

/// Creates [LocSetStrategy].
public class LocSetStrategyFactory implements StrategyFactory {
    @Override
    public LocSetStrategy create(Proof proof, StrategyProperties strategyProperties) {
        return new LocSetStrategy(proof, strategyProperties);
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        return new StrategySettingsDefinition("LocSet Options");
    }

    @Override
    public Name name() {
        return LocSetStrategy.NAME;
    }
}
