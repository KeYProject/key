/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.exploration.actions;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.exploration.ExplorationModeModel;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Common functionalities for proof exploration actions.
 */
@NullMarked
public abstract class ExplorationAction extends MainWindowAction {

    private static final long serialVersionUID = -1662459714803539089L;

    protected ExplorationAction(MainWindow mw) {
        super(mw);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
    }

    @Nullable
    JTerm promptForTerm(MainWindow window, @Nullable JTerm term) {
        final String initialValue;
        if (term == null) {
            initialValue = "";
        } else {
            Services services = getMediator().getServices();
            if (services == null) {
                throw new NullPointerException("No services available.");
            }
            initialValue = LogicPrinter.quickPrintTerm(term, services);
        }

        JTerm result = null;

        while (result == null) {
            String input = JOptionPane.showInputDialog(window, "Input a formula:", initialValue);
            if (input == null) {
                return null;
            }

            Services services = window.getMediator().getServices();
            if (services == null) {
                throw new NullPointerException("No services available.");
            }
            KeyIO io = new KeyIO(services);
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
        ExplorationModeModel model = getMediator().lookup(ExplorationModeModel.class);
        if (model == null) {
            throw new NullPointerException("Exploration mode model is not registered.");
        }
        return model;
    }
}
