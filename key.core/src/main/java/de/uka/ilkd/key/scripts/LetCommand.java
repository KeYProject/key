/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.scripts;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.scripts.meta.Documentation;
import de.uka.ilkd.key.scripts.meta.OptionalVarargs;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

import org.jspecify.annotations.NullMarked;

/// The *let* command lets you introduce entries to the abbreviation table.
/// ```
/// let @abbrev1=term1 ... @abbrev2=term2;
/// ```
/// or
/// ```
/// letf @abbrev1=term1 ... @abbrev2=term2;
/// ```
/// **Arguments:**
/// - varargs any key-value where *value* is a term and key is prefixed with `@`
///
/// If `letf` is used instead of `let`, existing bindings are overridden; otherwise a conflicting
/// name results in an exception.
@NullMarked
public class LetCommand extends AbstractCommand {

    // Changes:
    // * Apr,2025 (weigl): remove "force" in favor of "letf".
    // * Jan,2025 (weigl): add new parameter "force" to override bindings.

    @Documentation(category = "Fundamental",
        value = """
                Each argument is a key-value pair `@name=term`. With `let`, a name that is already
                bound results in an exception; `letf` overrides the existing binding.
                """)


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
            if (key.startsWith("#") || key.equals("force")) {
                continue;
            }

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
