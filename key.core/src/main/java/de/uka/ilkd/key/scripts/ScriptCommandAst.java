/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.parser.Location;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static java.util.stream.Collectors.joining;

/// This class represents is the AST of a proof script command.
///
/// It is an abstraction to the commands of following structure:
/// ```
/// <commandName> key_1=value_1 ... key_m=value_m positionalArgs_1 ... positionalArgs_n {
/// commands_0; ...; commands_k;
/// }
/// ```
///
/// @param commandName the name of the command, e.g., "macro" for `macro auto;`
/// @param namedArgs a map of the given named arguments and values.
/// If a named argument is not given, the entry should be missing in the map. Null-values are not
/// allowed.
/// @param positionalArgs the list of given positional arguments
/// @param commands a nullable block of proof script arguments (represents "higher-order proof
/// scripts").
/// If null, the block was omitted syntactically in contrast to an empty list.
/// @param location the location of this command for error reporting.
/// @author Alexander Weigl
/// @version 1 (14.03.25)
@NullMarked
public record ScriptCommandAst(
        String commandName,
        Map<String, Object> namedArgs,
        List<Object> positionalArgs,
        @Nullable List<ScriptCommandAst> commands,
        @Nullable Location location) {

    public ScriptCommandAst(String commandName, Map<String, Object> namedArgs,
            List<Object> positionalArgs) {
        this(commandName, namedArgs, positionalArgs, Collections.emptyList(), null);
    }

    public String asCommandLine() {
        return commandName + ' ' +
                namedArgs.entrySet().stream()
                        .map(it -> it.getKey() + ": " + humanString(it.getValue()))
                        .collect(joining(" "))
                + ' '
                + positionalArgs.stream().map(ScriptCommandAst::humanString).collect(joining(" "))
                + (commands != null
                        ? " {"
                            + commands.stream().map(ScriptCommandAst::asCommandLine)
                                    .collect(joining("\n"))
                            + "\n}"
                        : ";");
    }

    public static String humanString(Object value) {
        if (value instanceof ParserRuleContext ctx) {
            return ctx.getText();
        }
        return Objects.toString(value);
    }
}
