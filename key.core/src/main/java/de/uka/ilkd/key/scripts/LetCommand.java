/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

import org.jspecify.annotations.NullMarked;

/// The *let* command lets you introduce entries to the abbreviation table.
/// ```
/// let @abbrev1=term1 ... @abbrev2=term2;
/// ```
/// of
/// ```
/// letf @abbrev1=term1 ... @abbrev2=term2;
/// ```
/// **Arguments:**
/// - varargs any key-value where *value* is a term and key is prefixed with `@`
///
/// **Aliases**
/// - `letf` if used, the let bindings are overridden otherwise conflicts results into an exception.
///
/// **Changes:**
/// * Apr,2025 (weigl): remove {@code force} in favor of {@code letf}.
/// * Jan,2025 (weigl): add new parameter {@code force} to override bindings.
@NullMarked
public class LetCommand implements ProofScriptCommand {
    @Override
    public List<ProofScriptArgument> getArguments() {
        return List.of();
    }


    @Override
    public void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState stateMap) throws ScriptException, InterruptedException {

        AbbrevMap abbrMap = stateMap.getAbbreviations();

        boolean force = "letf".equals(args.commandName());

        for (Map.Entry<String, Object> entry : args.namedArgs().entrySet()) {
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
                final var value = termCtx.accept(stateMap.getEvaluator());
                final var term = stateMap.getValueInjector().convert(value, JTerm.class);
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

    @Override
    public List<String> getAliases() {
        return List.of(getName(), "letf");
    }
}
