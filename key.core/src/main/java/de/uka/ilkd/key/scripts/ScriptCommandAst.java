/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.parser.Location;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * This class represents is the AST of a proof script command.
 *
 * @param commandName the name of the command, e.g., "macro" for {@code macro auto;}
 * @param namedArgs a map of the given named arguments and values. If a named argument is not given,
 *        the entry should be missing in the map. Null-values are not allowed.
 * @param positionalArgs the list of given positional arguments
 * @param commands a nullable block of proof script arguments (represents "higher-order proof
 *        scripts")
 * @param location the location of this command for error reporting.
 * @author Alexander Weigl
 * @version 1 (14.03.25)
 */
@NullMarked
public record ScriptCommandAst(
        String commandName,
        Map<String, Object> namedArgs,
        List<Object> positionalArgs,
        @Nullable List<ScriptCommandAst> commands,
        @Nullable Location location) {
}
