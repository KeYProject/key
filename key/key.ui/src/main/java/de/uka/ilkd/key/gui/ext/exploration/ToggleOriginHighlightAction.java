package de.uka.ilkd.key.gui.ext.exploration;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.IconFactory;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.ext.KeYExtConst;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.ViewSettings;

/**
 * Action to toggle {@link ViewSettings#isHighlightOrigin()}.
 *
 * @author lanzinger
 */
public class ToggleOriginHighlightAction extends MainWindowAction {

    /**
     * Create a new action.
     *
     * @param mainWindow the main window.
     */
    public ToggleOriginHighlightAction(MainWindow mainWindow) {
        super(mainWindow);
        setIcon(IconFactory.originHighlightIcon());
        setEnabled(true);
        setSelected(ProofIndependentSettings.DEFAULT_INSTANCE
                .getViewSettings().isHighlightOrigin());

        putValue(KeYExtConst.PATH, "Origin Tracking");
        setName("Highlight Origins");
        setTooltip("When moving the mouse over a term in the sequent view,"
                + "highlight its origin in the source view.");
        putValue(KeYExtConst.CHECKMARK, true);

        ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings().addSettingsListener(
                event -> {
            boolean useOriginLabels = ProofIndependentSettings.DEFAULT_INSTANCE
                    .getTermLabelSettings().getUseOriginLabels();

            setEnabled(useOriginLabels);
        });
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        boolean oldValue = ProofIndependentSettings.DEFAULT_INSTANCE
                .getViewSettings().isHighlightOrigin();
        ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setHighlightOrigin(!oldValue);
    }
}
