/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;

import de.uka.ilkd.key.parser.Location;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static java.util.stream.Collectors.joining;

/// This class represents a block `{ c1; c2; ... ck; }` of proof scripts.
@NullMarked
public record ScriptBlock(
        List<ScriptCommandAst> commands,
        @Nullable Location location) {

    /// Renders this command a parsable string representation. The order of the arguments is as
    /// follows:
    /// key-value arguments, positional arguments and the additional script block.
    ///
    /// @see de.uka.ilkd.key.nparser.ParsingFacade#parseScript(org.antlr.v4.runtime.CharStream)
    public String asCommandLine() {
        if (commands.isEmpty()) {
            return " {}";
        }
        if (commands.size() == 1) {
            return " {" + commands.getFirst().asCommandLine() + "}";
        }

        return " {\n"
            + commands.stream().map(ScriptCommandAst::asCommandLine).collect(joining("\n"))
            + "\n}";
    }
}
