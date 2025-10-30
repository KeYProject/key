/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.Path;

import de.uka.ilkd.key.scripts.meta.Argument;

import de.uka.ilkd.key.scripts.meta.Documentation;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Includes and runs another script file.
 * See Parameters for more documentation.
 */
public class ScriptCommand extends AbstractCommand {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ProofScriptCommand.class);

    public ScriptCommand() {
        super(Parameters.class);
    }

    @Documentation(category = "Control", value = "Includes and runs another script file.")
    public static class Parameters {
        @Documentation("The filename of the script to include. May be relative to the current script.")
        @Argument
        public @MonotonicNonNull String filename;
    }

    @Override
    public void execute(ScriptCommandAst ast) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), ast);
        Path root = state().getBaseFileName();
        if (!Files.isDirectory(root)) {
            root = root.getParent();
        }
        Path file = root.resolve(args.filename);

        LOGGER.info("Included script {}", file);

        try {
            ProofScriptEngine pse = new ProofScriptEngine(proof);
            pse.setCommandMonitor(state().getObserver());
            pse.execute(uiControl, file);
        } catch (NoSuchFileException e) {
            // The message is very cryptic otherwise.
            throw new ScriptException("Script file '" + file + "' not found", e);
        } catch (Exception e) {
            throw new ScriptException("Error while running script'" + file + "': " + e.getMessage(),
                e);
        }
    }

    @Override
    public String getName() {
        return "script";
    }
}
