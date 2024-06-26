/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.awt.event.InputEvent;
import java.util.Iterator;
import java.util.Objects;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.SpecNameLabel;
import de.uka.ilkd.key.pp.AbbrevException;
import de.uka.ilkd.key.proof.Node;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Scans through the current sequent and introduce an abbreviation for each named term.
 * A named term is a term labeled with a {@link SpecNameLabel}.
 *
 * @author Alexander Weigl
 * @version 1 (1/16/22)
 */
public class MakeNamedFormulaToAbbrevAction extends MainWindowAction {
    private final static Logger LOGGER =
        LoggerFactory.getLogger(MakeNamedFormulaToAbbrevAction.class);

    public MakeNamedFormulaToAbbrevAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Introduce abbreviation for named formulas");
        setEnabled(mainWindow.getMediator().getSelectedNode() != null);
        mainWindow.getMediator().addKeYSelectionListener(new KeYSelectionListener() {
            @Override
            public void selectedNodeChanged(KeYSelectionEvent<Node> e) {
                setEnabled(mainWindow.getMediator().getSelectedNode() != null);
            }
        });
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        var node = Objects.requireNonNull(mainWindow.getMediator().getSelectedNode());
        findAndIntroduce(node.sequent().antecedent().iterator());
        findAndIntroduce(node.sequent().succedent().iterator());

        if ((e.getModifiers() & InputEvent.SHIFT_DOWN_MASK) != 0) {
            mainWindow.getVisibleTermLabels().setHidden(SpecNameLabel.NAME, true);
        }

        mainWindow.makePrettyView();
    }

    private void findAndIntroduce(Iterator<SequentFormula> iterator) {
        iterator.forEachRemaining(it -> findAndIntroduce(it.formula()));
    }

    private void findAndIntroduce(Term t) {
        var l = (SpecNameLabel) t.getLabel(SpecNameLabel.NAME);
        if (l != null) {
            try {
                getMediator().getNotationInfo().getAbbrevMap().put(t, l.label(), true);
                LOGGER.info("Activate abbreviation @{} with {}", l.label(), t);
            } catch (AbbrevException e) {
                LOGGER.error("Could not activate abbreviation @{} with {}", l.label(), t);
            }
        }

        for (Term sub : t.subs()) {
            findAndIntroduce(sub);
        }
    }
}
