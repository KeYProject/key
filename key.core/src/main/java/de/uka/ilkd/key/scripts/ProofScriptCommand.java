/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.List;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

import org.jspecify.annotations.NullMarked;

/// A [ProofScriptCommand] is an executable mutation on the given proof. It abstracts complex
/// operations, and made them accessible for an API.
///
/// [ProofScriptCommand] are supported by the java.util.[java.util.ServiceLoader]. You
/// can add new proof script commands by add a new entry to
/// <code>META-INF/service/de.uka.ilkd.key.macros.scripts.ProofScriptCommand</code>.
///
/// **Version 2 (2017-03-28):** change of the interface support for structured arguments.
///
/// @author Mattias Ulbrich
/// @author Alexander Weigl
@NullMarked
public interface ProofScriptCommand {

    /// Self-documentation of this command by returning a list of descriptions for arguments.
    /// @return an unmodifiable list of [ProofScriptArgument]
    List<ProofScriptArgument> getArguments();

    /// @param uiControl the current ui controller
    /// @param args the script arguments
    /// @param stateMap the current state
    /// @throws ScriptException if something bad happens
    /// @throws InterruptedException if something bad happens
    // TODO downgrade AbstractUserInterfaceControl to UserInterfaceControl
    void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState stateMap)
            throws ScriptException, InterruptedException;

    /// Returns the name of this proof command. The name should be constant and not be clash with
    /// the
    /// name of other commands. The name is essential for finding this command within an hashmap.
    ///
    /// @return a non-null, non-empty string
    /// @see ProofScriptEngine
    String getName();

    /// Announce a list of potential aliases of this command.
    ///
    /// The command can react differently for each alias. The call name is given to
    /// [#execute(AbstractUserInterfaceControl,ScriptCommandAst,EngineState)]
    /// inside [ScriptCommandAst]. For example [LetCommand] announce `letf` as an
    /// alias for an overwriting binding, otherwise error are thrown on re-binding.
    ///
    /// @return an unmodifiable list of alias names under which command can be called, including
    /// [#getName()]
    default List<String> getAliases() {
        return List.of(getName());
    }

    /// A documentation for the commands.
    ///
    /// @return a non-null string
    String getDocumentation();
}
