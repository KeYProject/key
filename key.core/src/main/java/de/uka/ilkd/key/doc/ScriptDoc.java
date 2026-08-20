/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.doc;

import java.util.ArrayList;
import java.util.Comparator;

import de.uka.ilkd.key.scripts.ProofScriptCommand;
import de.uka.ilkd.key.scripts.ProofScriptEngine;

/**
 *
 * @author Alexander Weigl
 * @version 1 (23.08.26)
 */
public class ScriptDoc {
    public static void main(String[] args) {
        var commands = new ArrayList<>(ProofScriptEngine.loadCommands().values());
        commands.sort(Comparator.comparing(ProofScriptCommand::getName));

        for (var command : commands) {
            System.out.println(command.getDocumentation());
            System.out.println("\n\n\n");
        }
    }
}
