/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.io.File;
import java.nio.file.NoSuchFileException;

import de.uka.ilkd.key.macros.scripts.meta.Option;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ScriptCommand extends AbstractCommand<ScriptCommand.Parameters> {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(ProofScriptCommand.class);

    public ScriptCommand() {
        super(Parameters.class);
    }

    public static class Parameters {
        @Option("#2")
        public String filename;
    }

    @Override
    public void execute(Parameters args) throws ScriptException, InterruptedException {
        File root = state.getBaseFileName();
        if (!root.isDirectory()) {
            root = root.getParentFile();
        }
        File file = new File(root, args.filename);

        LOGGER.info("Included script " + file);

        try {
            ProofScriptEngine pse = new ProofScriptEngine(file);
            pse.setCommandMonitor(state.getObserver());
            pse.execute(uiControl, proof);
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
