/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.pp.AbbrevMap;

public class LetCommand extends AbstractCommand<Map<String, String>> {

    public LetCommand() {
        super(null);
    }

    @Override
    public Map<String, String> evaluateArguments(EngineState state, Map<String, String> arguments) {
        return arguments;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Map<String, String> args,
            EngineState stateMap) throws ScriptException, InterruptedException {

        AbbrevMap abbrMap = stateMap.getAbbreviations();
        for (Map.Entry<String, String> entry : args.entrySet()) {
            String key = entry.getKey();
            if ("#1".equals(key)) {
                continue;
            }
            if ("#literal".equals(key)) {
                continue;
            }
            if (!key.startsWith("@")) {
                throw new ScriptException("Unexpected parameter to let, only @var allowed: " + key);
            }

            // get rid of @
            key = key.substring(1);

            if (abbrMap.containsAbbreviation(key)) {
                // XXX desired or not?
                throw new ScriptException(key + " is already fixed in this script");
            }
            try {
                abbrMap.put(stateMap.toTerm(entry.getValue(), null), key, true);
            } catch (Exception e) {
                throw new ScriptException(e);
            }
        }

    }

    @Override
    public String getName() {
        return "let";
    }

}
