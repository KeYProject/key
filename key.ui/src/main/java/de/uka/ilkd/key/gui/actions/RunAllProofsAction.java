/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.ui.MediatorProofControl;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class provides an action for KeY UI which runs a set of specified proof files automatically.
 * The intent of this class is to have a massive test feature for the quality assurance of the KeY
 * during the release preparation.
 * <p>
 * The used proofs can be given by the environment {@link #ENV_VARIABLE}. If this variable is not
 * set, this class use the default {@code de/uka/ilkd/key/gui/actions/runallproofsui.txt}. See
 * method {@link #loadFiles()} for more details.
 *
 * @author weigl
 */
@NullMarked
public class RunAllProofsAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(RunAllProofsAction.class);

    /**
     * Environment variable which points to a text file with the KeY-files to be loaded.
     */
    public static final String ENV_VARIABLE = "KEY_RUNALLPROOFS_UI_FILE";

    /**
     * Filename of the user-defined input files.
     */
    private static final @Nullable String RUN_ALL_PROOFS_UI = System.getenv(ENV_VARIABLE);

    /**
     * Default file name for lookup in the classpath.
     */
    private static final String DEFAULT_FILE = "runallproofsui.txt";

    /**
     * Path to the directory of built-in examples.
     */
    private final Path exampleDir;

    /**
     * Files to loaded
     */
    private List<Path> files;

    /**
     * Loads the key file given in the file by environment variable {@link #ENV_VARIABLE}. If the
     * content of {@link #ENV_VARIABLE} ({@link #RUN_ALL_PROOFS_UI}) is null, then
     * {@link #DEFAULT_FILE} is used.
     */
    private List<Path> loadFiles() throws IOException {
        LOGGER.info("Use 'export {}=<...>' to set the input file for {}.", ENV_VARIABLE,
            getClass().getSimpleName());

        InputStream stream;
        if (RUN_ALL_PROOFS_UI == null) {
            stream = getClass().getResourceAsStream(DEFAULT_FILE);
            if (stream == null) {
                LOGGER.error("Could not find {} in the classpath.", DEFAULT_FILE);
                return Collections.emptyList();
            }
        } else {
            stream = new FileInputStream(RUN_ALL_PROOFS_UI);
        }

        try (BufferedReader in =
            new BufferedReader(new InputStreamReader(stream, StandardCharsets.UTF_8))) {
            return in.lines()
                    .filter(it -> !it.startsWith("#") && !it.trim().isEmpty())
                    .map(it -> (it.startsWith("/")
                            ? Paths.get(it)
                            : exampleDir.resolve(it))
                            .toAbsolutePath())
                    .toList();
        }
    }

    /**
     * The action-configuration calls in this constructor operate on {@code this} while the
     * receiver is still under initialization (EISOP initialization check); safe here, suppressed
     * with a scoped key. The examples directory lookup must succeed: this action runs the
     * pre-defined example proofs and is only constructed after {@code PathConfig} setup.
     */
    @SuppressWarnings("nullness:method.invocation.invalid")
    public RunAllProofsAction(MainWindow mainWindow) {
        super(mainWindow);

        Main.ensureExamplesAvailable();
        Path examplesDir = Main.getExamplesDir();
        if (examplesDir == null) {
            throw new NullPointerException("No examples directory configured.");
        }
        exampleDir = examplesDir;

        try {
            files = loadFiles();
        } catch (IOException e) {
            files = new ArrayList<>();
            LOGGER.warn("Failed to load files");
        }

        setName("Run all proofs");
        setTooltip(
            "Open and run a pre-defined set of proofs for GUI testing. Enabled with KeY debug flag");
    }

    /**
     * The problem loader is created with deliberately {@code null} class path, boot class path
     * and includes: a {@code null} value selects the defaults (empty/classpath-based) per
     * {@code JavaModel}/{@code SLEnvInput} semantics, as used by all other problem-loading entry
     * points; the legacy parameters are annotated {@code @NonNull}, suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    @Override
    public void actionPerformed(ActionEvent e) {
        WindowUserInterfaceControl ui = mainWindow.getUserInterface();

        for (int i = 0; i < files.size(); i++) {
            LOGGER.info("{}: {}\n", i, files.get(i));
        }

        Runnable runnable = () -> {
            for (Path absFile : files) {
                ui.reportStatus(this, "Run: " + absFile);
                LOGGER.info("Run: {}", absFile);
                ProblemLoader problemLoader =
                    ui.getProblemLoader(absFile, null, null, null, getMediator());
                problemLoader.runSynchronously();
                LOGGER.info("Loaded: {}", absFile);

                KeYMediator r = getMediator();
                Proof proof = r.getSelectedProof();
                MediatorProofControl control = ui.getProofControl();
                // {@code getSelectedProof()} may be {@code null} (no proof loaded); the proof
                // control rejects a {@code null} proof anyway, so skip the auto-mode start.
                if (proof != null && control.isAutoModeSupported(proof)) {
                    control.startAutoMode(proof, proof.openEnabledGoals());
                    control.waitWhileAutoMode();
                }
                Proof selectedProof = getMediator().getSelectedProof();
                if (selectedProof == null) {
                    throw new NullPointerException("No proof selected after loading.");
                }
                LOGGER.info("Finish: ({}) {}", selectedProof.closed(), absFile);
                selectedProof.dispose();
            }
            LOGGER.info("==== RUN ALL PROOFS FINISHED ==== ");
        };
        Thread t = new Thread(runnable);
        t.start();
    }
}
