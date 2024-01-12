/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.macros.scripts.meta.DescriptionFacade;
import de.uka.ilkd.key.macros.scripts.meta.ProofScriptArgument;

/**
 * @author Alexander Weigl
 * @version 1 (28.03.17)
 */
public abstract class NoArgumentCommand implements ProofScriptCommand<Void> {
    @Override
    public List<ProofScriptArgument<Void>> getArguments() {
        return new ArrayList<>();
    }

    @Override
    public Void evaluateArguments(EngineState state, Map<String, String> arguments) {
        return null;
    }

    @Override
    public String getDocumentation() {
        return DescriptionFacade.getDocumentation(this);
    }
}
