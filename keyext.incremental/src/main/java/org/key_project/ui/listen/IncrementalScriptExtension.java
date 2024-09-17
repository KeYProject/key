/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package org.key_project.ui.listen;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import javax.annotation.Nonnull;
import javax.swing.*;
import javax.swing.filechooser.FileNameExtensionFilter;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.extension.api.KeYGuiExtension;
import de.uka.ilkd.key.java.statement.JmlAssert;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.macros.ApplyScriptsMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ScriptAwareMacro;
import de.uka.ilkd.key.macros.scripts.ProofScriptEngine;
import de.uka.ilkd.key.macros.scripts.ScriptException;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoader;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlLexer;
import de.uka.ilkd.key.speclang.njml.JmlParser;
import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@KeYGuiExtension.Info(name = "Incremental scripting",
    description = "Apply scripts locally w/o reparsing everything if possible. Author: Mattias Ulbrich <ulbrich@kit.edu>",
    experimental = false,
    optional = true,
    priority = 10000)
public class IncrementalScriptExtension implements KeYGuiExtension, KeYGuiExtension.Toolbar,
    KeYGuiExtension.Startup, KeYSelectionListener {

    public static final Logger LOGGER = LoggerFactory.getLogger(IncrementalScriptExtension.class);

    private static final ProofMacro MACRO = new ScriptAwareMacro();
    private static final Name JML_ASSERT = new Name("JML assert");
    private JToolBar theToolbar;
    private String keyFile;
    private Snapshot snapshot;
    private MainWindow mainWindow;

    @Override
    public void selectedNodeChanged(KeYSelectionEvent e) {
        // nothing to do
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        // TODO: this only partially works at the moment!
        // use information from originally loaded key file for incremental script reloading
        Proof p = mainWindow.getMediator().getSelectedProof();
        File f = p.getProofFile();
        if (f != null && (f.toString().endsWith(".proof") || f.toString().endsWith(".key"))) {
            if (keyFile == null) {
            keyFile = f.getAbsolutePath();

            try {
                snapshot = Snapshot.fromFile(keyFile);
                snapshot.setProof(p);
            } catch (ProofInputException | IOException ex) {
                throw new RuntimeException(ex);
            }
            }
        }
    }
    private class ChooseFile extends MainWindowAction {

        public ChooseFile(MainWindow mainWindow) {
            super(mainWindow);
            setName("Choose file");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            try {
                KeYFileChooser chooser = KeYFileChooser.getFileChooser("Select file to load");
                chooser.setFileFilter(KeYFileChooser.KEY_FILTER);
                int returnVal = chooser.showOpenDialog(null);
                if (returnVal == JFileChooser.APPROVE_OPTION) {
                    keyFile = chooser.getSelectedFile().getAbsolutePath();
                    reload();
                }
            } catch (Exception ex) {
                IssueDialog.showExceptionDialog(mainWindow, ex);
            }
        }
    }

    private class RefreshAction extends MainWindowAction {
        public RefreshAction(MainWindow mainWindow) {
            super(mainWindow);
            setName("Refresh proof");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            if (keyFile == null) {
                JOptionPane.showMessageDialog(mainWindow, "Please choose a .key file first.");
                return;
            }
            try {
                refreshProof();
            } catch (Exception ex) {
                IssueDialog.showExceptionDialog(mainWindow, ex);
            }
        }
    }

    // compare scripts, reload file if necessary, prune assertions and re-apply scripts (if changed)
    private void refreshProof() throws ProofInputException, IOException, ScriptException {
        Snapshot newSnapshot = Snapshot.fromFile(keyFile);
        if (!snapshot.equalsOutsideScripts(newSnapshot)) {
            reload();
        } else {
            mainWindow.getMediator().setProof(snapshot.getProof());
            Set<String> changedScripts = snapshot.getChangedScripts(newSnapshot);
            if(!changedScripts.isEmpty()) {
                Map<String, String> newScripts = new HashMap<>();
                for (String scriptName : changedScripts) {
                    newScripts.put(scriptName, newSnapshot.getScript(scriptName));
                }
                applyScripts(newScripts);
                newSnapshot.setProof(snapshot.getProof());
                snapshot = newSnapshot;
            }
        }
    }

    // for changed scripts: prune back to assertion node and re-run
    private void applyScripts(Map<String, String> newScripts) throws IOException, ScriptException {
        List<Node> todo = new LinkedList<>();
        Proof proof = snapshot.getProof();
        todo.add(proof.root());
        while (!todo.isEmpty()) {
            Node node = todo.remove(0);
            JmlAssert assertion = ApplyScriptsMacro.getJmlAssert(node);

            if(assertion == null || assertion.getOptLabel() == null ||
                    !newScripts.containsKey(assertion.getOptLabel()) ||
                    node.parent().child(0) != node) {
                // This is not the first child of an assertion node -> descend in proof tree
                for (int i = 0; i < node.childrenCount(); i++) {
                    todo.add(node.child(i));
                }
                continue;
            }

            // This is an assertion proof node.
            proof.pruneProof(node);
            String newScript = newScripts.get(assertion.getOptLabel());
            var cmds = parseScript(newScript);
            String renderedProof = ApplyScriptsMacro.renderProof(cmds, node.sequent().succedent().getLast().formula(), proof.getServices());
            Path script = Files.createTempFile("key.script", "key");
            Files.writeString(script, renderedProof);
            script.toFile().deleteOnExit();
            Location loc = new Location(script.toUri().toURL(), 0, 0);
            Goal goal = proof.getGoal(node);
            ProofScriptEngine pse = new ProofScriptEngine(renderedProof, loc, goal);
            LOGGER.info("Running script");
            LOGGER.info(renderedProof);
            try {
                pse.execute(mainWindow.getUserInterface(), proof);
            } catch (ScriptException e) {
                int line = e.getLocation() == null ? 0 : e.getLocation().getLine();
                throw new ScriptException("Failed to run the following script in line " +
                        line + ":\n" + renderedProof, Location.fromPositionInfo(assertion.getPositionInfo()), e);
            } catch (InterruptedException e) {
                throw new ScriptException(e);
            }
        }
    }

    private List<JmlParser.ProofCmdContext> parseScript(String script) {
        JmlLexer jmlLexer = JmlFacade.createLexer(script);
        jmlLexer.pushMode(JmlLexer.script);
        jmlLexer.bracesLevel = 1;
        JmlParser jmlParser = JmlFacade.createParser(jmlLexer);
        return jmlParser.proofCmdsEOF().proofCmd();
    }

    private void reload() throws ProofInputException, IOException {
        snapshot = Snapshot.fromFile(keyFile);

        final ProblemLoader pl =
                new ProblemLoader(new File(keyFile), null, null, null,
                        AbstractProfile.getDefaultProfile(), false,
                        mainWindow.getMediator(), true, null,
                        mainWindow.getUserInterface());
        pl.runSynchronously();
        snapshot.setProof(mainWindow.getMediator().getSelectedProof());
        mainWindow.getMediator().getUI().getProofControl().runMacro(snapshot.getProof().root(), MACRO, null);
    }

    @Nonnull
    @Override
    public JToolBar getToolbar(MainWindow mainWindow) {
        if (theToolbar == null) {
            JToolBar bar = new JToolBar();
            bar.add(new JButton(new ChooseFile(mainWindow)));
            bar.add(new JButton(new RefreshAction(mainWindow)));
            theToolbar = bar;
        }
        return theToolbar;
    }

    @Override
    public void init(MainWindow window, KeYMediator mediator) {
        this.mainWindow = window;
        mediator.addKeYSelectionListenerChecked(this);
    }
}
