/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.scripts.meta.ProofScriptArgument;

/**
 * A {@link ProofScriptCommand} is an executable mutation on the given proof. It abstracts complex
 * operations, and made them accessible for an API.
 * <p>
 * {@link ProofScriptCommand} are supported by the java.util.{@link java.util.ServiceLoader}. You
 * can add new proof script commands by add a new entry to
 * <code>META-INF/service/de.uka.ilkd.key.macros.scripts.ProofScriptCommand</code>.
 * <p>
 * <b>Version 2 (2017-03-28):</b> change of the interface support for structured arguments.
 * </p>
 *
 * @param <T> the arguments
 * @author Mattias Ulbrich
 * @author Alexander Weigl
 */
public interface ProofScriptCommand<T> {

    /**
     *
     */
    List<ProofScriptArgument<T>> getArguments();

    /**
     * @param arguments
     * @return
     */
    T evaluateArguments(EngineState state, Map<String, String> arguments) throws Exception;

    /**
     * @param uiControl the current ui controller
     * @param args the script arguments
     * @param stateMap the current state
     * @throws ScriptException if something bad happens
     * @throws InterruptedException if something bad happens
     */
    // TODO downgrade AbstractUserInterfaceControl to UserInterfaceControl
    void execute(AbstractUserInterfaceControl uiControl, T args, EngineState stateMap)
            throws ScriptException, InterruptedException;

    /**
     * Returns the name of this proof command. The name should be constant and not be clash with the
     * name of other commands. The name is essential for finding this command within an hashmap.
     *
     * @return a non-null, non-empty string
     * @see ProofScriptEngine
     */
    String getName();

    /**
     * A documentation for the commands.
     *
     * @return a non-null string
     */
    String getDocumentation();
}
