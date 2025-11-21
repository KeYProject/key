/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;
import java.util.Map;
import java.util.Objects;

import de.uka.ilkd.key.nparser.KeYParser;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.parser.Location;

import org.antlr.v4.runtime.ParserRuleContext;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

import static java.util.stream.Collectors.joining;

/// This class represents is the AST of a proof script command.
///
/// It is an abstraction to the commands of following structure:
/// ```
/// integer-split
/// "<0" : { auto; }
/// "=0" : { instantiate; }
/// ">0" : { tryclose; }
/// ;
/// ```
/// or
/// ```
/// <commandName> key_1:value_1 ... key_m:value_m positionalArgs_1 ... positionalArgs_n;
/// ```
/// where `value_X` and `positionalArgs_X` can also be scripts.
///
/// @param commandName the name of the command, e.g., "macro" for `macro auto;`
/// @param namedArgs a map of the given named arguments and values.
/// If a named argument is not given, the entry should be missing in the map. Null-values are not
/// allowed.
/// @param positionalArgs the list of given positional arguments
/// @param location the location of this command for error reporting. **excluded from equality**
/// @author Alexander Weigl
/// @version 1 (14.03.25)
@NullMarked
public record ScriptCommandAst(
        String commandName,
        Map<String, Object> namedArgs,
        List<Object> positionalArgs,
        @Nullable Location location) {

    public ScriptCommandAst(String commandName, Map<String, Object> namedArgs,
            List<Object> positionalArgs) {
        this(commandName, namedArgs, positionalArgs, null);
    }

    /// Renders this command a parsable string representation. The order of the arguments is as
    /// follows:
    /// key-value arguments, positional arguments and the additional script block.
    ///
    /// @see de.uka.ilkd.key.nparser.ParsingFacade#parseScript(CharStream)
    public String asCommandLine() {
        return commandName + ' ' +
            namedArgs.entrySet().stream()
                    .map(it -> it.getKey() + ": " + asReadableString(it.getValue()))
                    .collect(joining(" "))
            + ' '
            + positionalArgs.stream().map(ScriptCommandAst::asReadableString)
                    .collect(joining(" "))
            + ";";
    }

    public static String asReadableString(Object value) {
        if (value instanceof ScriptBlock b) {
            return b.asCommandLine();
        }

        if (value instanceof KeYParser.ProofScriptCodeBlockContext ctx) {
            asReadableString(KeyAst.ProofScript.asAst(null, ctx));
        }
        if (value instanceof ParserRuleContext ctx) {
            return ctx.getText();
        }
        return Objects.toString(value);
    }

    @Override
    public int hashCode() {
        return Objects.hash(commandName, namedArgs, positionalArgs);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null || getClass() != obj.getClass()) {
            return false;
        }
        ScriptCommandAst other = (ScriptCommandAst) obj;
        return Objects.equals(commandName, other.commandName)
                && Objects.equals(positionalArgs, other.positionalArgs)
                && Objects.equals(namedArgs, other.namedArgs);
    }
}
