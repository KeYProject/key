/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.scripts.meta.DescriptionFacade;
import de.uka.ilkd.key.macros.scripts.meta.ProofScriptArgument;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * @author Alexander Weigl
 * @version 1 (28.03.17)
 */
public abstract class NoArgumentCommand implements ProofScriptCommand<Void> {
    @Override
    public List<ProofScriptArgument> getArguments() {
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
