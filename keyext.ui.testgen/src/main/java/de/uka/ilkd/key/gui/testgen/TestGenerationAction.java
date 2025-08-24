/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.testgen;

import java.awt.event.ActionEvent;
import javax.swing.*;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;


/**
 * Action which generates test cases for all open nodes. If the proof is closed, test cases will be
 * generated for nodes on which the emptyModality rule was applied.
 *
 * @author mihai
 */
public class TestGenerationAction extends MainWindowAction {
    private static final String NAME = "Generate Testcases...";
    private static final String TOOLTIP = "Generate test cases for open goals";
    private static final String TOOLTIP_EXTRA = ". Install Z3 to enable this functionality!";

    public TestGenerationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName(NAME);
        setTooltip(TOOLTIP);
        Icon icon = IconFactory.testGeneration(MainWindow.TOOLBAR_ICON_SIZE);
        setSmallIcon(icon);
        setMenuPath("Proof");

        enabledOnAnActiveProof();
        enabledOnAnActiveProof();

        ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().addPropertyChangeListener(
            e -> updateEnabledness());
        Pred z3CE = this::checkZ3CE;
        setEnabledWhen(getEnabledWhen().and(z3CE));
    }

    /**
     * @return whether Z3 is installed
     */
    private boolean checkZ3CE() {
        var haveZ3CE = SolverTypes.Z3_CE_SOLVER.isInstalled(false);
        if (!haveZ3CE) {
            setTooltip(TOOLTIP + TOOLTIP_EXTRA);
        } else if (!isEnabled()) {
            setTooltip(TOOLTIP);
        }
        return haveZ3CE;
    }


    @Override
    public void actionPerformed(ActionEvent e) {
        TGInfoDialog dlg = new TGInfoDialog(mainWindow);
        dlg.setVisible(true);
        dlg.setLocationRelativeTo(mainWindow);
    }
}
