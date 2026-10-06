/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

/// Creates [SetStrategy].
public class SetStrategyFactory implements StrategyFactory {
    @Override
    public SetStrategy create(Proof proof, StrategyProperties strategyProperties) {
        return new SetStrategy(proof, strategyProperties);
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        return new StrategySettingsDefinition("Set Options");
    }

    @Override
    public Name name() {
        return SetStrategy.NAME;
    }
}
