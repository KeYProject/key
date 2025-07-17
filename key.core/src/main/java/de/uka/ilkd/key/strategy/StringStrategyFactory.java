/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;

import org.key_project.logic.Name;

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
