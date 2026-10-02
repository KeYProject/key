/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

/// Creates [StringStrategy].
public class StringStrategyFactory implements StrategyFactory {
    @Override
    public StringStrategy create(Proof proof, StrategyProperties strategyProperties) {
        return new StringStrategy(proof, strategyProperties);
    }

    @Override
    public StrategySettingsDefinition getSettingsDefinition() {
        return new StrategySettingsDefinition("String Options");
    }

    @Override
    public Name name() {
        return StringStrategy.NAME;
    }
}
