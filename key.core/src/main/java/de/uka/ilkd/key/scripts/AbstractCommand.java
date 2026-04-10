/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.meta.ArgumentsLifter;
import de.uka.ilkd.key.scripts.meta.ProofScriptArgument;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/// A base class for {@link ProofScriptCommand}s.
/// This class brings automatically analyzes and meta-data of the given parameter class using
/// reflection and
/// decorators.
///
/// To implement your own command, you need to define two classes a POJO carrying the parameters,
/// and child class of
/// {@link AbstractCommand}. You need to override [AbstractCommand#execute(Object)] to implement the
/// command logic.
///
/// @author Alexander Weigl
@NullMarked
public abstract class AbstractCommand implements ProofScriptCommand {
    protected @Nullable Proof proof;
    protected @Nullable Services service;
    protected @Nullable EngineState state;
    protected @Nullable AbstractUserInterfaceControl uiControl;

    /**
     * Documentation of this command.
     */
    protected @Nullable String documentation = null;

    protected final EngineState state() {
        return Objects.requireNonNull(state);
    }

    /**
     * ...
     */
    private final @Nullable Class<?> parameterClazz;

    protected AbstractCommand(@Nullable Class<?> clazz) {
        this.parameterClazz = clazz;
    }

    public List<ProofScriptArgument> getArguments() {
        if (parameterClazz == null) {
            return new ArrayList<>();
        }
        return ArgumentsLifter.inferScriptArguments(parameterClazz);
    }


    @Override
    public final void execute(AbstractUserInterfaceControl uiControl, ScriptCommandAst args,
            EngineState stateMap)
            throws ScriptException, InterruptedException {
        proof = stateMap.getProof();
        service = proof.getServices();
        state = stateMap;
        this.uiControl = uiControl;

        try {
            execute(args);
        } finally {
            // preventing memory leak
            proof = null;
            service = null;
            state = null;
        }
    }

    /// Executes the command logic with the given parameters `args`.
    ///
    /// @param args an instance of the parameters
    /// @throws ScriptException if something happened during execution
    /// @throws InterruptedException if thread was interrupted during execution
    public void execute(ScriptCommandAst args) throws ScriptException, InterruptedException {
    }

    @Override
    public String getDocumentation() {
        if (documentation == null && parameterClazz != null) {
            documentation =
                ArgumentsLifter.extractDocumentation(getName(), getClass(), parameterClazz);
        }
        return Objects.requireNonNullElse(documentation, "");
    }

}
