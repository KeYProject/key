/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;
import java.util.Objects;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.exploration.ExplorationModeModel;

/**
 * Common functionalities for proof exploration actions.
 */
public abstract class ExplorationAction extends MainWindowAction {

    private static final long serialVersionUID = -1662459714803539089L;

    public ExplorationAction(MainWindow mw) {
        super(mw);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
    }

    Term promptForTerm(MainWindow window, Term term) {
        final String initialValue =
            term == null ? "" : LogicPrinter.quickPrintTerm(term, getMediator().getServices());

        Term result = null;

        while (result == null) {
            String input = JOptionPane.showInputDialog(window, "Input a formula:", initialValue);
            if (input == null) {
                return null;
            }

            KeyIO io = new KeyIO(window.getMediator().getServices());
            try {
                result = io.parseExpression(input);

                if (term != null && !result.sort().equals(term.sort())) {
                    JOptionPane.showMessageDialog(window,
                        String.format("%s is of sort %s, but we need a term of sort %s", result,
                            result.sort(), term.sort()),
                        "Sort mismatch", JOptionPane.ERROR_MESSAGE);
                    result = null;
                }
            } catch (BuildingException e) {
                JOptionPane.showMessageDialog(window, e.getMessage(), "Malformed input",
                    JOptionPane.ERROR_MESSAGE);
            }
        }

        return result;
    }

    public ExplorationModeModel getModel() {
        return Objects.requireNonNull(getMediator().lookup(ExplorationModeModel.class));
    }
}
