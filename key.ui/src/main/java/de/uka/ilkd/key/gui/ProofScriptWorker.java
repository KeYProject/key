/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.*;
import java.awt.Dialog.ModalityType;
import java.net.URI;
import java.util.List;
import java.util.concurrent.CancellationException;
import java.util.function.Consumer;
import javax.swing.*;
import javax.swing.text.BadLocationException;
import javax.swing.text.Document;

import de.uka.ilkd.key.core.InterruptListener;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionModel;
import de.uka.ilkd.key.nparser.KeyAst;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.scripts.ProofScriptEngine;
import de.uka.ilkd.key.scripts.ScriptException;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Executes s given script.
 */
@NullMarked
public class ProofScriptWorker extends SwingWorker<@Nullable Object, ProofScriptEngine.Message>
        implements InterruptListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(ProofScriptWorker.class);

    private final KeYMediator mediator;
    private final KeyAst.ProofScript script;

    /**
     * The initially selected goal.
     */
    private final @Nullable Goal initiallySelectedGoal;

    /**
     * The proof script engine.
     */
    private final ProofScriptEngine engine;
    private final JDialog monitor = new JDialog(MainWindow.getInstance(),
        "Running Script ...", ModalityType.MODELESS);
    private final JTextArea logArea = new JTextArea();

    private final Consumer<ProofScriptEngine.Message> observer = this::publish;

    /**
     * Instantiates a new proof script worker.
     *
     * @param mediator the mediator
     * @param script the script
     */
    public ProofScriptWorker(KeYMediator mediator, KeyAst.ProofScript script) {
        this(mediator, script, null);
    }

    /**
     * Instantiates a new proof script worker.
     *
     * @param mediator the mediator
     * @param script the script
     * @param initiallySelectedGoal the initially selected goal
     */
    public ProofScriptWorker(KeYMediator mediator, KeyAst.ProofScript script,
            @Nullable Goal initiallySelectedGoal) {
        this.mediator = mediator;
        this.script = script;
        this.initiallySelectedGoal = initiallySelectedGoal;
        engine = new ProofScriptEngine(script, initiallySelectedGoal);
    }

    @Override
    protected @Nullable Object doInBackground() throws Exception {
        try {
            engine.setCommandMonitor(observer);
            engine.execute(mediator.getUI(), mediator.getSelectedProof());
        } catch (InterruptedException ex) {
            LOGGER.debug("Proof macro has been interrupted:", ex);
        }
        return null;
    }

    private void makeDialog() {
        URI uri = script.getStartLocation().getFileURI().orElse(null);
        Container cp = monitor.getContentPane();
        logArea.setFont(new Font(Font.MONOSPACED, Font.PLAIN, 12));
        logArea.setEditable(false);
        logArea.setText("Running script from URL '" + uri + "':\n");
        cp.add(new JScrollPane(logArea), BorderLayout.CENTER);

        JButton cancelButton = new JButton("Cancel");
        cancelButton.addActionListener(e -> interruptionPerformed());
        JPanel panel = new JPanel(new FlowLayout());
        panel.add(cancelButton);
        cp.add(panel, BorderLayout.SOUTH);

        monitor.setSize(750, 400);
        monitor.setLocationRelativeTo(MainWindow.getInstance());
    }

    @Override
    protected void process(List<ProofScriptEngine.Message> chunks) {
        Document doc = logArea.getDocument();
        for (ProofScriptEngine.Message info : chunks) {
            var message = new StringBuilder("\n---\n");
            if (info instanceof ProofScriptEngine.EchoMessage(String msg)) {
                message.append(msg);
            } else {
                var exec = (ProofScriptEngine.ExecuteInfo) info;
                if (exec.command().startsWith("'echo ")) {
                    continue;
                }
                if (exec.location().getFileURI().isPresent()) {
                    message.append(exec.location().getFileURI().get()).append(":");
                }
                message.append(exec.location().getPosition().line())
                        .append(": Executing on goal ").append(exec.nodeSerial()).append('\n')
                        .append(exec.command());
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
        mediator.initiateAutoMode(initiallySelectedGoal != null ? initiallySelectedGoal.proof()
                : mediator.getSelectedProof(),
            true, false);
        mediator.addInterruptedListener(this);
        makeDialog();
        monitor.setVisible(true);
    }

    /*
     * finalise the GUI stuff
     */
    @Override
    public void done() {
        monitor.setVisible(false);

        try {
            get();
        } catch (CancellationException ex) {
            LOGGER.info("Scripting was cancelled.");
        } catch (Throwable ex) {
            LOGGER.error("", ex);
            IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
        }

        mediator.removeInterruptedListener(this);

        final Proof proof = initiallySelectedGoal != null ? initiallySelectedGoal.proof()
                : mediator.getSelectedProof();
        mediator.finishAutoMode(proof, true, true, this::selectGoalOrNode);
    }

    private void selectGoalOrNode() {
        final KeYSelectionModel selectionModel = mediator.getSelectionModel();
        if (!mediator.getSelectedProof().closed()) {
            try {
                selectionModel
                        .setSelectedGoal(engine.getStateMap().getFirstOpenAutomaticGoal());
                return;
            } catch (ScriptException e) {
                LOGGER.warn("Script threw exception", e);
            } catch (Exception e) {
                LOGGER.warn("Unexpected exception", e);
            }
        }
        selectionModel.defaultSelection();
    }

    @Override
    public void interruptionPerformed() {
        // just notify the thread that the button has been pressed
        cancel(true);
    }

}
