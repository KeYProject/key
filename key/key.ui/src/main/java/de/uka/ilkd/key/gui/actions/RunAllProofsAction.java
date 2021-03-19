package de.uka.ilkd.key.gui.actions;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ExampleChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.WindowUserInterfaceControl;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.ui.MediatorProofControl;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.awt.event.ActionEvent;
import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * This class provides an action for KeY UI which runs a set of specified proof files automatically.
 * The intent of this class is to have a massive test feature for the quality assurance of the KeY during the
 * release preparation.
 *
 * The used proofs can be given by the environment {@link #ENV_VARIABLE}.
 * If this variable is not set, this class use the default {@code de/uka/ilkd/key/gui/actions/runallproofsui.txt}.
 * See method {@link #loadFiles()} for more details.
 *
 * @author weigl
 */
public class RunAllProofsAction extends MainWindowAction {
    public static final String ENV_VARIABLE = "KEY_RUNALLPROOFS_UI_FILE";
    private static final @Nullable String RUN_ALL_PROOFS_UI = System.getenv(ENV_VARIABLE);
    private static final String DEFAULT_FILE = "runallproofsui.txt";
    private final File EXAMPLE_DIR = ExampleChooser.lookForExamples();
    private List<File> files;

    /**
     * Loads the key file given in the file by environment variable {@link #ENV_VARIABLE}.
     * If the content of {@link #ENV_VARIABLE} ({@link #RUN_ALL_PROOFS_UI}) is null,
     * then {@link #DEFAULT_FILE} is used.
     */
    private @NotNull  List<File> loadFiles() throws IOException {
        System.out.format("INFO: Use 'export %s=<...>' to set the input file for %s.\n",
                ENV_VARIABLE, getClass().getSimpleName());

        InputStream stream;
        if (RUN_ALL_PROOFS_UI == null) {
            stream = getClass().getResourceAsStream(DEFAULT_FILE);
        } else {
            stream = new FileInputStream(RUN_ALL_PROOFS_UI);
        }


        try (BufferedReader in = new BufferedReader(new InputStreamReader(stream))) {
            return in.lines()
                    .filter(it -> !it.startsWith("#") && !it.trim().isEmpty())
                    .map(it -> (it.startsWith("/") ? new File(it) : new File(EXAMPLE_DIR, it)).getAbsoluteFile())
                    .collect(Collectors.toList());
        }
    }

    public RunAllProofsAction(MainWindow mainWindow) {
        super(mainWindow);
        try {
            files = loadFiles();
        } catch (IOException e) {
            files = new ArrayList<>();
            e.printStackTrace();
        }
        setName("Run all proofs");
        //setEnabled(Debug.ENABLE_DEBUG);
        setTooltip("Open and run a pre-defined set of proofs for GUI testing. Enabled with KeY debug flag");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        WindowUserInterfaceControl ui = mainWindow.getUserInterface();

        for (int i = 0; i < files.size(); i++) {
            System.out.format("%2d: %s\n", i, files.get(i));
        }

        Runnable runnable = () -> {
            for (File absFile : files) {
                ui.reportStatus(this, "Run: " + absFile);
                System.out.println("Run:" + absFile);
                ProblemLoader problemLoader = ui.getProblemLoader(absFile, null, null, null, getMediator());
                problemLoader.runSynchronously();
                //mainWindow.loadProblem(absFile);
                System.out.println("Loaded:" + absFile);

                KeYMediator r = getMediator();
                Proof proof = r.getSelectedProof();
                MediatorProofControl control = ui.getProofControl();
                if (control.isAutoModeSupported(proof)) {
                    control.startAutoMode(proof, proof.openEnabledGoals());
                    control.waitWhileAutoMode();
                }
                System.out.println("Finish: (" + getMediator().getSelectedProof().closed() + ") " + absFile);
                getMediator().getSelectedProof().dispose();
            }
            System.out.println("==== RUN ALL PROOFS FINISHED ==== ");
        };
        Thread t = new Thread(runnable);
        t.start();
        /*
        List<ExampleChooser.Example> examples = ExampleChooser.listExamples(exampleDir);
        for (ExampleChooser.Example example : examples) {
            File obl = example.getObligationFile();
            mainWindow.loadProblem(obl);
        }*/
    }
}
