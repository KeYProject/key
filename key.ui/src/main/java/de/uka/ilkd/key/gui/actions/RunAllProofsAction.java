/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.ui.MediatorProofControl;

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
public class RunAllProofsAction extends MainWindowAction {
    private static final Logger LOGGER = LoggerFactory.getLogger(RunAllProofsAction.class);

    /**
     * Environment variable which points to a text file with the KeY-files to be loaded.
     */
    public static final String ENV_VARIABLE = "KEY_RUNALLPROOFS_UI_FILE";

    /**
     * Filename of the user-defined input files.
     */
    @Nullable
    private static final String RUN_ALL_PROOFS_UI = System.getenv(ENV_VARIABLE);

    /**
     * Default file name for lookup in the classpath.
     */
    private static final String DEFAULT_FILE = "runallproofsui.txt";

    /**
     * Path to the directory of built-in examples.
     */
    private final File exampleDir;

    /**
     * Files to loaded
     */
    private List<File> files;


    /**
     * Loads the key file given in the file by environment variable {@link #ENV_VARIABLE}. If the
     * content of {@link #ENV_VARIABLE} ({@link #RUN_ALL_PROOFS_UI}) is null, then
     * {@link #DEFAULT_FILE} is used.
     */
    @Nonnull
    private List<File> loadFiles() throws IOException {
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
            return in.lines().filter(it -> !it.startsWith("#") && !it.trim().isEmpty())
                    .map(it -> (it.startsWith("/") ? new File(it) : new File(exampleDir, it))
                            .getAbsoluteFile())
                    .collect(Collectors.toList());
        }
    }

    public RunAllProofsAction(MainWindow mainWindow) {
        super(mainWindow);

        Main.ensureExamplesAvailable();
        exampleDir = new File(Main.getExamplesDir());

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

    @Override
    public void actionPerformed(ActionEvent e) {
        WindowUserInterfaceControl ui = mainWindow.getUserInterface();

        for (int i = 0; i < files.size(); i++) {
            LOGGER.info("{}: {}\n", i, files.get(i));
        }

        Runnable runnable = () -> {
            for (File absFile : files) {
                ui.reportStatus(this, "Run: " + absFile);
                LOGGER.info("Run: {}", absFile);
                ProblemLoader problemLoader =
                    ui.getProblemLoader(absFile, null, null, null, getMediator());
                problemLoader.runSynchronously();
                LOGGER.info("Loaded: {}", absFile);

                KeYMediator r = getMediator();
                Proof proof = r.getSelectedProof();
                MediatorProofControl control = ui.getProofControl();
                if (control.isAutoModeSupported(proof)) {
                    control.startAutoMode(proof, proof.openEnabledGoals());
                    control.waitWhileAutoMode();
                }
                LOGGER.info("Finish: ({}) {}", getMediator().getSelectedProof().closed(), absFile);
                getMediator().getSelectedProof().dispose();
            }
            LOGGER.info("==== RUN ALL PROOFS FINISHED ==== ");
        };
        Thread t = new Thread(runnable);
        t.start();
    }
}
