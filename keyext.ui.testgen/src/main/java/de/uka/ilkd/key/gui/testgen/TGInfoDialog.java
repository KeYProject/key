/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.testgen;

import java.awt.*;
import java.awt.event.ActionEvent;
import javax.swing.*;
import javax.swing.text.DefaultCaret;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.testgen.smt.testgen.TestGenerationLog;
import de.uka.ilkd.key.util.ThreadUtilities;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class TGInfoDialog extends JDialog {
    private static final Logger LOGGER = LoggerFactory.getLogger(TGInfoDialog.class);
    private final JTextArea textArea;
    private final JButton stopButton;
    private final JButton exitButton;
    private final JButton startButton;

    private transient TGWorker worker;

    private final KeyAction actionStop = new KeyAction() {
        {
            setName("Stop");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            // This method delegates the request only to the UserInterfaceControl
            // which implements the functionality. No functionality is allowed in this method body!
            new Thread(() -> {
                MainWindow.getInstance().getMediator().getUI().getProofControl()
                        .stopAndWaitAutoMode();
                ThreadUtilities.invokeOnEventQueue(() -> exitButton.setEnabled(true));
            }).start();
        }
    };

    private final AbstractAction actionExit = new KeyAction() {
        {
            setName("Exit");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            TGInfoDialog.this.dispose();
        }
    };

    private final KeyAction actionStart = new KeyAction() {
        {
            setName("Start");
        }

        @Override
        public void actionPerformed(ActionEvent e) {
            worker = new TGWorker(TGInfoDialog.this);
            worker.start();
        }
    };

    private final TestGenerationLog logger = new TestGenerationLog() {
        @Override
        public void write(String t) {
            textArea.append(t);
        }

        @Override
        public void writeln(String line) {
            ThreadUtilities.invokeOnEventQueue(() -> textArea.append(line + "\n"));
        }

        @Override
        public void writeException(Throwable t) {
            LOGGER.warn("Exception", t);
            ThreadUtilities.invokeOnEventQueue(() -> textArea.append("Error: " + t.getMessage()));
        }

        @Override
        public void testGenerationCompleted() {
            ThreadUtilities.invokeOnEventQueue(() -> exitButton.setEnabled(true));
        }
    };

    public TGInfoDialog(Window owner) {
        super(owner);

        // init members
        textArea = new JTextArea();
        stopButton = new JButton(actionStop);
        exitButton = new JButton(actionExit);
        startButton = new JButton(actionStart);

        // configure properties
        setModal(false);
        setTitle("Test Suite Generation");
        setSize(1000, 700);
        setDefaultCloseOperation(WindowConstants.DISPOSE_ON_CLOSE);
        setLayout(new BorderLayout());

        final JScrollPane scrollpane = new JScrollPane(textArea);
        final DefaultCaret caret = (DefaultCaret) textArea.getCaret();
        final JPanel flowPanel = new JPanel(new FlowLayout());

        scrollpane.setHorizontalScrollBarPolicy(ScrollPaneConstants.HORIZONTAL_SCROLLBAR_AS_NEEDED);
        scrollpane.setVerticalScrollBarPolicy(ScrollPaneConstants.VERTICAL_SCROLLBAR_ALWAYS);
        caret.setUpdatePolicy(DefaultCaret.ALWAYS_UPDATE);
        exitButton.setEnabled(false);

        // build ui tree
        flowPanel.add(startButton);
        flowPanel.add(stopButton);
        flowPanel.add(exitButton);
        add(scrollpane, BorderLayout.CENTER);
        add(flowPanel, BorderLayout.SOUTH);
        add(new TestgenOptionsPanel(), BorderLayout.EAST);
    }

    public KeyAction getActionStop() {
        return actionStop;
    }

    public AbstractAction getActionExit() {
        return actionExit;
    }

    public KeyAction getActionStart() {
        return actionStart;
    }

    public TestGenerationLog getLogger() {
        return logger;
    }
}
