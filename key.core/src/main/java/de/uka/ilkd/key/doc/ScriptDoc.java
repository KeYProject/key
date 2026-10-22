/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

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
        new ScriptDoc().run(args[0], args[1]);
    }

    @Override
    protected List<DocItem> collectData() {
        var items = new ArrayList<DocItem>();
        for (var command : sortedCommands()) {
            var parameters = new ArrayList<DocParameter>();
            for (ProofScriptArgument meta : command.getArguments()) {
                String kind = meta.isFlag() ? "flag" : meta.isOption() ? "option" : "positional";
                parameters.add(new DocParameter(meta.getName(),
                    meta.getType().getSimpleName(),
                    cleanJavadoc(meta.getDocumentation()),
                    kind,
                    meta.isRequired(),
                    meta.isPositional() ? meta.getArgumentPosition() : null,
                    meta.isPositionalVarArgs() || meta.isOptionalVarArgs()));
            }

            var signature = new DocSignature(parameters, "", false);
            items.add(new DocItem(command.getName(),
                cleanJavadoc(command.getDocumentation()),
                List.of(signature),
                command.getCategory(),
                command.getClass().isAnnotationPresent(Deprecated.class)));
        }
        return items;
    }

    /// Returns all loaded proof script commands sorted by their name.
    private List<ProofScriptCommand> sortedCommands() {
        var commands = new ArrayList<>(ProofScriptEngine.loadCommands().values());
        commands.sort(Comparator.comparing(ProofScriptCommand::getName));
        return commands;
    }
}
