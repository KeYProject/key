/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.scripts.ProofScriptCommand;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

/**
 * Generates the markdown documentation of all proof script commands (loaded via
 * {@link ProofScriptEngine#loadCommands()}), based on their self-documentation.
 *
 * @author Alexander Weigl
 * @version 1 (23.08.26)
 */
public class ScriptDoc extends AbstractDocGenerator {

    public static void main(String[] args) throws Exception {
        new ScriptDoc().run(args);
    }

    @Override
    protected void generateDocumentation(PrintStream out) {
        for (var command : sortedCommands()) {
            out.println();
            out.println();
            out.format("### `%s`\n\n", command.getName());
            out.println(cleanJavadoc(command.getDocumentation()));
        }
    }

    @Override
    protected Object generateJsonData() {
        var commands = new ArrayList<Map<String, Object>>();
        for (var command : sortedCommands()) {
            var data = new LinkedHashMap<String, Object>();
            data.put("name", command.getName());
            data.put("category", command.getCategory());
            data.put("deprecated", command.getClass().isAnnotationPresent(Deprecated.class));
            data.put("documentation", cleanJavadoc(command.getDocumentation()));

            var arguments = new ArrayList<Map<String, Object>>();
            for (ProofScriptArgument meta : command.getArguments()) {
                var argument = new LinkedHashMap<String, Object>();
                argument.put("name", meta.getName());
                argument.put("type", meta.getType().getSimpleName());
                argument.put("kind",
                    meta.isFlag() ? "flag" : meta.isOption() ? "option" : "positional");
                argument.put("required", meta.isRequired());
                if (meta.isPositional()) {
                    argument.put("position", meta.getArgumentPosition());
                }
                if (meta.isPositionalVarArgs() || meta.isOptionalVarArgs()) {
                    argument.put("varargs", true);
                }
                argument.put("description", meta.getDocumentation());
                arguments.add(argument);
            }
            data.put("arguments", arguments);
            commands.add(data);
        }
        return Map.of("commands", commands);
    }

    /// Returns all loaded proof script commands sorted by their name.
    private List<ProofScriptCommand> sortedCommands() {
        var commands = new ArrayList<>(ProofScriptEngine.loadCommands().values());
        commands.sort(Comparator.comparing(ProofScriptCommand::getName));
        return commands;
    }
}
