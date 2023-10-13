/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.BorderLayout;
import java.awt.Dimension;
import java.awt.event.ActionEvent;
import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JDialog;
import javax.swing.JTextArea;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofScriptWorker;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.parser.Location;

/**
 * The Class ProofScriptInputAction.
 *
 * @author lanzinger
 */
public class ProofScriptInputAction extends AbstractAction {

    private static final long serialVersionUID = -1193756128644859298L;

    /** The mediator. */
    private final KeYMediator mediator;

    /**
     * Instantiates a new proof script input action.
     *
     * @param mediator the mediator
     */
    public ProofScriptInputAction(KeYMediator mediator) {
        super("Input proof script...");
        this.mediator = mediator;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Window win = new Window(MainWindow.getInstance(), mediator);
        win.setVisible(true);
    }

    private static final class Window extends JDialog {

        private static final long serialVersionUID = -6219149431583804843L;

        private Window(MainWindow mainWindow, KeYMediator mediator) {
            super(mainWindow, "Enter proof script");

            JTextArea textArea = new JTextArea();
            JButton okButton = new JButton("OK");

            okButton.addActionListener(event -> {
                ProofScriptWorker psw = new ProofScriptWorker(mediator, textArea.getText(),
                    new Location(null, Position.newOneBased(1, 1)),
                    mediator.getSelectedGoal());

                dispose();

                psw.init();
                psw.execute();
            });

            setLayout(new BorderLayout());
            add(textArea, BorderLayout.CENTER);
            add(okButton, BorderLayout.PAGE_END);

            setSize(new Dimension(mainWindow.getWidth() / 3, mainWindow.getHeight() / 2));
            setLocationRelativeTo(mainWindow);
        }
    }
}
