/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

public class SymExStrategyFactory implements StrategyFactory {
    @Override
    public SymExStrategy create(Proof proof, StrategyProperties strategyProperties) {
        return new SymExStrategy(proof);
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        return null;
    }

    @Override
    public Name name() {
        return SymExStrategy.NAME;
    }
}
