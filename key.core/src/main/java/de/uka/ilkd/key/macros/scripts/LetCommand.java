/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.scripts.meta.ProofScriptArgument;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.pp.AbbrevMap;

/// The *let* command lets you introduce entries to the abbreviation table.
/// ```
/// let @abbrev1=term1 ... @abbrev2=term2 force=true;
/// ```
/// **Arguments:**
/// - varargs any key-value where *value* is a term and key is prefixed with `@`
/// - `force` : `boolean` if set the bindings are overridden otherwise conflicts results into an
/// exception.
///
/// **Changes:**
/// * Jan,2025 (weigl): add new parameter {@code force} to override bindings.
public class LetCommand implements ProofScriptCommand<Map<String, Object>> {

    @Override
    public List<ProofScriptArgument<Map<String, Object>>> getArguments() {
        return List.of();
    }

    @Override
    public Map<String, Object> evaluateArguments(EngineState state, Map<String, Object> arguments) {
        return arguments;
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Map<String, Object> args,
            EngineState stateMap) throws ScriptException, InterruptedException {

        AbbrevMap abbrMap = stateMap.getAbbreviations();

        boolean force = args.containsKey("force");

        for (Map.Entry<String, Object> entry : args.entrySet()) {
            String key = entry.getKey();
            if (key.startsWith("#") || key.equals("force")) {
                continue;
            }

            if (!key.startsWith("@")) {
                throw new ScriptException("Unexpected parameter to let, only @var allowed: " + key);
            }

            // get rid of @
            key = key.substring(1);

            if (abbrMap.containsAbbreviation(key) && !force) {
                throw new ScriptException(key + " is already fixed in this script");
            }
            try {
                final var termCtx = (KeYParser.ProofScriptExpressionContext) entry.getValue();
                final var term = stateMap.getEvaluator().visitTerm(termCtx.term());
                abbrMap.put(term, key, true);
            } catch (Exception e) {
                throw new ScriptException(e);
            }
        }

    }

    @Override
    public String getName() {
        return "let";
    }

    @Override
    public String getDocumentation() {
        return "";
    }
}
