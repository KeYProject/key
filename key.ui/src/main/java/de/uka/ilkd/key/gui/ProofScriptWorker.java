/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.Dialog.ModalityType;
import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.util.List;
import java.util.concurrent.*;
import java.util.function.Consumer;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;

import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ProofScriptWorker extends SwingWorker<Object, ProofScriptEngine.Message>
        implements InterruptListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofScriptWorker.class);

    private final KeYMediator mediator;
    private final String script;
    private final Location initialLocation;

    /** The initially selected goal. */
    private final Goal initiallySelectedGoal;

    /** The proof script engine. */
    private ProofScriptEngine engine;
    private JDialog monitor;
    private JTextArea logArea;

    private final Consumer<ProofScriptEngine.Message> observer = this::publish;

    public ProofScriptWorker(KeYMediator mediator, File file) throws IOException {
        this.initialLocation = new Location(file.toURI(), Position.newOneBased(1, 1));
        this.script = Files.readString(file.toPath());
        this.mediator = mediator;
        this.initiallySelectedGoal = null;
    }

    /**
     * Instantiates a new proof script worker.
     *
     * @param mediator the mediator
     * @param script the script
     * @param location the location
     */
    public ProofScriptWorker(KeYMediator mediator, String script, Location location) {
        this(mediator, script, location, null);
    }

    /**
     * Instantiates a new proof script worker.
     *
     * @param mediator the mediator
     * @param script the script
     * @param location the location
     * @param initiallySelectedGoal the initially selected goal
     */
    public ProofScriptWorker(KeYMediator mediator, String script, Location location,
            Goal initiallySelectedGoal) {
        this.mediator = mediator;
        this.script = script;
        this.initialLocation = location;
        this.initiallySelectedGoal = initiallySelectedGoal;
    }

    @Override
    protected Object doInBackground() throws Exception {
        try {
            engine = new ProofScriptEngine(script, initialLocation, initiallySelectedGoal);
            engine.setCommandMonitor(observer);
            engine.execute(mediator.getUI(), mediator.getSelectedProof());
        } catch (InterruptedException ex) {
            LOGGER.debug("Proof macro has been interrupted:", ex);
        }
        return null;
    }

    private void makeDialog() {
        URI uri = initialLocation.getFileURI().orElse(null);

        if (monitor != null) {
            logArea.setText("Running script from URL '" + uri + "':\n");
            return;
        }

        JDialog dlg =
            new JDialog(MainWindow.getInstance(), "Running Script ...", ModalityType.MODELESS);
        Container cp = dlg.getContentPane();
        logArea = new JTextArea();
        logArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
        logArea.setEditable(false);
        logArea.setText("Running script from URL '" + uri + "':\n");
        cp.add(new JScrollPane(logArea), BorderLayout.CENTER);

        JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(e -> interruptionPerformed());
        JPanel panel = new JPanel(new FlowLayout());
        panel.add(cancelButton);
        cp.add(panel, BorderLayout.SOUTH);

        dlg.setSize(750, 400);
        dlg.setLocationRelativeTo(MainWindow.getInstance());

        this.monitor = dlg;
    }

    @Override
    protected void process(List<ProofScriptEngine.Message> chunks) {
        Document doc = logArea.getDocument();
        for (ProofScriptEngine.Message info : chunks) {
            var message = new StringBuilder("\n---\n");
            if (info instanceof ProofScriptEngine.EchoMessage) {
                var echo = (ProofScriptEngine.EchoMessage) info;
                message.append(echo.message);
            } else {
                var exec = (ProofScriptEngine.ExecuteInfo) info;
                if (exec.command.startsWith("'echo ")) {
                    continue;
                }
                if (exec.location.getFileURI().isPresent()) {
                    message.append(exec.location.getFileURI().get()).append(":");
                }
                message.append(exec.location.getPosition().line())
                        .append(": Executing on goal ").append(exec.nodeSerial).append('\n')
                        .append(exec.command);
            }
            try {
                doc.insertString(doc.getLength(), message.toString(), null);
            } catch (BadLocationException e) {
                LOGGER.warn("Failed to insert string", e);
            }
        }
    }

    /*
     * initiate the GUI stuff and relay to superclass
     */
    public void init() {
        mediator.stopInterface(true);
        mediator.setInteractive(false);
        mediator.addInterruptedListener(this);
        makeDialog();
        monitor.setVisible(true);
    }

    /*
     * finalise the GUI stuff
     */
    @Override
    public void done() {
        if (monitor != null) {
            monitor.setVisible(false);
        }

        try {
            get();
        } catch (CancellationException ex) {
            LOGGER.info("Scripting was cancelled.");
        } catch (Throwable ex) {
            LOGGER.error("", ex);
            IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
        }

        mediator.removeInterruptedListener(this);
        runWithDeadline(() -> mediator.startInterface(true), 1000);
        runWithDeadline(() -> mediator.getUI().getProofControl().stopAndWaitAutoMode(), 1000);

        try {
            if (!mediator.getSelectedProof().closed()) {
                mediator.getSelectionModel()
                        .setSelectedGoal(engine.getStateMap().getFirstOpenAutomaticGoal());
            }
        } catch (ScriptException e) {
            LOGGER.warn("", e);
        }

        mediator.setInteractive(true);
    }

    private static void runWithDeadline(Runnable runnable, int milliseconds) {
        final ExecutorService executor = Executors.newFixedThreadPool(1);
        final Future<?> future = executor.submit(runnable);
        executor.shutdown();
        try {
            future.get(1000, TimeUnit.MILLISECONDS);
        } catch (InterruptedException | ExecutionException | TimeoutException e) {
            /*
             * NOTE (DS, 2019-02-08): There are some problems in starting the automode... We will
             * just don't do anything here and hope that everything works fine (which it did for my
             * tests). Any Java-multithreading experts around? ;)
             */
        }
    }

    @Override
    public void interruptionPerformed() {
        // just notify the thread that the button has been pressed
        cancel(true);
    }

}
