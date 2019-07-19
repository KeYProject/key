package de.uka.ilkd.key.gui.originlabels;

import java.awt.event.ActionEvent;

import bibliothek.gui.dock.common.CControl;
import bibliothek.gui.dock.common.DefaultMultipleCDockable;
import bibliothek.gui.dock.common.DefaultSingleCDockable;
import bibliothek.gui.dock.common.event.CDockableLocationEvent;
import bibliothek.gui.dock.common.event.CDockableLocationListener;
import bibliothek.gui.dock.common.event.CVetoClosingEvent;
import bibliothek.gui.dock.common.event.CVetoClosingListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.gui.docking.DockingHelper;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.settings.TermLabelSettings;

/**
 * Opens a {@link OriginTermLabelVisualizer} for the selected term.
 *
 * @author lanzinger
 */
public class ShowOriginAction extends MainWindowAction {

    private static DefaultMultipleCDockable dockable;

    private PosInSequent pos;

    /**
     * Creates a new {@link ShowOriginAction}.
     *
     * @param pos the position of the term whose origin shall be shown.
     */
    public ShowOriginAction(PosInSequent pos) {
        super(MainWindow.getInstance());
        this.pos = pos == null ? PosInSequent.createSequentPos() : pos;

        final TermLabelSettings settings =
                ProofIndependentSettings.DEFAULT_INSTANCE.getTermLabelSettings();

        setName("Show origin");
        setEnabled(settings.getUseOriginLabels());
        settings.addSettingsListener(event -> setEnabled(settings.getUseOriginLabels()));
        setMenuPath("View");
        lookupAcceleratorKey();
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        PosInOccurrence pio = pos.getPosInOccurrence();

        // OriginTermLabelVisualizer.TermView can only print sequents or formulas, not terms.
        if (pio != null) {
            while (!pio.subTerm().sort().equals(Sort.FORMULA)) {
                pio = pio.up();
            }
        }

        if (dockable == null) {
            dockable = new DefaultMultipleCDockable(null, IconFactory.ORIGIN_ICON.get(), "Origin");
        }

        OriginTermLabelVisualizer vis = new OriginTermLabelVisualizer(
                pio,
                getMediator().getSelectedNode(),
                getMediator().getServices());

        CControl dockControl = mainWindow.getDockControl();
        DefaultSingleCDockable dockable
            = (DefaultSingleCDockable) DockingHelper.createSingleDock(
                    vis.getShortName(), vis, vis.getLongName());

        dockable.setCloseable(true);
        dockable.addVetoClosingListener(new CVetoClosingListener() {

            @Override
            public void closed(CVetoClosingEvent event) {
                vis.dispose();
            }

            @Override
            public void closing(CVetoClosingEvent event) { }
        });
        dockable.addCDockableLocationListener(new CDockableLocationListener() {

            @Override
            public void changed(CDockableLocationEvent event) {
                if (!event.getNewShowing()) {
                    vis.hidden();
                }
            }
        });

        dockControl.addDockable(dockable);
        dockable.setLocationsAside(mainWindow.getDockSequent());
        dockable.setVisible(true);
        dockable.toFront();
    }
}
