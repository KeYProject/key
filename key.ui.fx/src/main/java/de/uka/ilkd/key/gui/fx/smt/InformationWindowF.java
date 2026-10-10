/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.smt;

import java.util.List;
import javafx.scene.Scene;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.scene.text.Font;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;

/**
 * The information window presents detailed information about the execution of an SMT solver,
 * counter-part of the Swing {@code de.uka.ilkd.key.gui.smt.InformationWindow}: one tab per
 * {@link Information} (error message, the SMT2 translation passed to the solver, the taclet
 * translation, the solver output, translation warnings).
 * <p>
 * KNOWN-SIMPLIFIED: the counterexample model tree ({@code CETree}) and the line numbers
 * ({@code TextLineNumber}) of the Swing original are not ported — the entries are presented as
 * read-only monospaced text areas, and the counterexample help tab (which the Swing original
 * adds with the model tree) is omitted with it.
 */
public final class InformationWindowF extends Stage {

    /**
     * One solver information entry, counter-part of the Swing
     * {@code InformationWindow.Information}.
     *
     * @param title the tab title
     * @param content the tab content
     * @param solver the solver that produced the content
     */
    public record Information(String title, String content, String solver) {
    }

    public InformationWindowF(Window owner, String title, List<Information> information) {
        setTitle(title);
        if (owner != null) {
            initOwner(owner);
        }

        TabPane tabs = new TabPane();
        tabs.setTabClosingPolicy(TabPane.TabClosingPolicy.UNAVAILABLE);
        for (Information el : information) {
            TextArea area = new TextArea(el.content());
            area.setEditable(false);
            area.setWrapText(false);
            // the solver input/output is SMT2 text; a monospaced font keeps it readable (the
            // Swing original used the sequent view font)
            area.setFont(Font.font("Monospaced", 13));
            tabs.getTabs().add(new Tab(el.title(), area));
        }

        Scene scene = new Scene(tabs, 640, 520);
        setScene(scene);
        ThemeManager.getInstance().manage(scene);
    }

    /**
     * Shows the information window for the given entries (Swing opens a non-modal
     * {@code JDialog} from {@code SolverListener.showInformation}).
     *
     * @param owner the owner window; may be {@code null}
     * @param title the window title
     * @param information the tabs to show
     */
    public static void show(Window owner, String title, List<Information> information) {
        new InformationWindowF(owner, title, information).show();
    }
}
