/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.parser.Location;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import java.util.List;

import static java.util.stream.Collectors.joining;

/// This class represents is the AST of a proof script command.
@NullMarked
public record ScriptBlock(
        List<ScriptCommandAst> commands,
        @Nullable Location location) {

    public String asCommandLine() {
        return " {"
                + commands.stream().map(ScriptCommandAst::asCommandLine).collect(joining("\n"))
                + "\n}";
    }
}
