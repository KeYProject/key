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
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.OptionalVarargs;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

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
public class LetCommand extends AbstractCommand {

    @Documentation(category = "Fundamental", value = """
        The let command lets you introduce entries to the abbreviation table.
        
            let @abbrev1=term1 ... @abbrev2=term2;

        or
        
            letf @abbrev1=term1 ... @abbrev2=term2;
   
        One or more key-value pairs are supported where key starts is @ followed by an identifier and
        value is a term.
        If letf if used instead of let, the let bindings are overridden otherwise conflicts results into an exception.""")


    public static class Parameters {
        @Documentation("Key-value pairs where key is the name of the abbreviation (starting with @) and value is a term.")
        @OptionalVarargs(as = JTerm.class)
        public Map<String, JTerm> namedArgs = Map.of();
    }

    public LetCommand() {
        super(Parameters.class);
    }

    @Override
    public List<ProofScriptArgument> getArguments() {
        return List.of();
    }

    public void execute(ScriptCommandAst ast) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), ast);

        AbbrevMap abbrMap = state().getAbbreviations();

        boolean force = "letf".equals(ast.commandName());

        for (Map.Entry<String, JTerm> entry : args.namedArgs.entrySet()) {
            String key = entry.getKey();

            if (key.startsWith("@")) {
                // get rid of @
                key = key.substring(1);
            }

            if (abbrMap.containsAbbreviation(key) && !force) {
                throw new ScriptException(key + " is already fixed in this script");
            }

            try {
                abbrMap.put(entry.getValue(), key, true);
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
    public List<String> getAliases() {
        return List.of(getName(), "letf");
    }
}
