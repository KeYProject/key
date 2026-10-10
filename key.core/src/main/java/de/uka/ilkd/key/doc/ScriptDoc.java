/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.doc;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Comparator;

import de.uka.ilkd.key.scripts.ProofScriptCommand;
import de.uka.ilkd.key.scripts.ProofScriptEngine;

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
        var commands = new ArrayList<>(ProofScriptEngine.loadCommands().values());
        commands.sort(Comparator.comparing(ProofScriptCommand::getName));

        for (var command : commands) {
            out.println();
            out.println();
            out.format("### `%s`\n\n", command.getName());
            out.println(cleanJavadoc(command.getDocumentation()));
        }
    }
}
