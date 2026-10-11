/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.smt;

import java.util.List;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.scene.control.Label;
import javafx.scene.control.ScrollPane;
import javafx.scene.control.Tab;
import javafx.scene.control.TabPane;
import javafx.scene.control.TextArea;
import javafx.scene.layout.BorderPane;
import javafx.scene.text.Font;
import javafx.scene.text.TextAlignment;
import javafx.stage.Stage;
import javafx.stage.Window;

import de.uka.ilkd.key.gui.fx.theme.ThemeManager;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;

/**
 * The information window presents detailed information about the execution of an SMT solver,
 * counter-part of the Swing {@code de.uka.ilkd.key.gui.smt.InformationWindow}: one tab per
 * {@link Information} (error message, the SMT2 translation passed to the solver, the taclet
 * translation, the solver output, translation warnings) with line numbers, and — for the Z3 CE
 * solver with a model — the "Counterexample" tab (the {@link CETreeF} model tree) and the "Help"
 * tab (the {@link #CE_HELP} text), WP-7 (Swing InformationWindow.initModel, :88-101).
 */
public final class InformationWindowF extends Stage {

    /**
     * The help text of the counterexample tab (Swing {@code InformationWindow.CE_HELP}).
     */
    public static final String CE_HELP =
        """
                Bounded Counterexample Finder for KeY Proof Obligations

                - Shows a bounded model which satisfies the negation of the selected proof obligation
                - Only proof obligations without modalities are supported
                - The OneStepSimplifier neeeds to be activated, otherwise updates need to be handled manually beforehand
                - Double click ond location set, sequence and object nodes(inside a heap) to extend them
                - Choose bit sizes in Options -> SMT Solvers
                - We have identified the following sources for spurious counterexample:
                   - Chosen bit sizes too small. Example: Bit size of Integer is 3 but literal 9 appears in proof obligation.
                   - Finite type instances: Example: There is no maximum integer.
                   - Removal of axioms. Example: There is a location set which contains location (o, f)""";

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

    public InformationWindowF(Window owner, SMTSolver solver, String title,
            List<Information> information) {
        setTitle(title);
        if (owner != null) {
            initOwner(owner);
        }

        TabPane tabs = new TabPane();
        tabs.setTabClosingPolicy(TabPane.TabClosingPolicy.UNAVAILABLE);
        initModel(solver, tabs);
        for (Information el : information) {
            tabs.getTabs().add(new Tab(el.title(), newTab(el)));
        }

        Scene scene = new Scene(tabs, 640, 520);
        setScene(scene);
        ThemeManager.getInstance().manage(scene);
    }

    /**
     * The counterexample model tabs (Swing {@code InformationWindow.initModel}, :88-101): for the
     * Z3 CE solver with a query model the window is retitled "Counterexample ..." and gets the
     * model tree and the help tab.
     *
     * @param solver the solver whose run is presented
     * @param tabs the tab pane to extend
     */
    private void initModel(SMTSolver solver, TabPane tabs) {
        if (solver.getType() != SolverTypes.Z3_CE_SOLVER) {
            return;
        }
        if (solver.getSocket().getQuery() == null) {
            return;
        }

        Model m = solver.getSocket().getQuery().getModel();
        setTitle("Counterexample " + getTitle());
        tabs.getTabs().add(new Tab("Counterexample", createModelTab(m)));
        createHelpTab(tabs);
    }

    /** The help tab (Swing {@code InformationWindow.createHelpTab}, :103-111). */
    private void createHelpTab(TabPane tabs) {
        TextArea content = new TextArea(CE_HELP);
        content.setEditable(false);
        content.setWrapText(true);
        tabs.getTabs().add(new Tab("Help", content));
    }

    /** The counterexample model tree tab (Swing {@code InformationWindow.createModelTab}). */
    private static Node createModelTab(Model model) {
        ScrollPane pane = new ScrollPane(new CETreeF(model).getTreeComponent());
        pane.setFitToWidth(true);
        pane.setFitToHeight(true);
        return pane;
    }

    /**
     * One information tab: the read-only, non-wrapping monospaced text with a simple line-number
     * gutter (the Swing original used {@code TextLineNumber}, InformationWindow.java:124-140).
     */
    private static Node newTab(Information information) {
        TextArea area = new TextArea(information.content());
        area.setEditable(false);
        area.setWrapText(false);
        // the solver input/output is SMT2 text; a monospaced font keeps it readable (the
        // Swing original used the sequent view font)
        area.setFont(Font.font("Monospaced", 13));

        BorderPane nowrap = new BorderPane(area);
        nowrap.setLeft(lineNumberGutter(area));
        ScrollPane pane = new ScrollPane(nowrap);
        pane.setFitToWidth(true);
        return pane;
    }

    /**
     * A simple line-number gutter for the given text area (FX has no {@code TextLineNumber}):
     * a right-aligned label whose lines follow the text and whose vertical offset follows the
     * scroll position.
     */
    private static Node lineNumberGutter(TextArea area) {
        Label gutter = new Label();
        gutter.setFont(area.getFont());
        gutter.setTextAlignment(TextAlignment.RIGHT);
        gutter.setAlignment(Pos.TOP_RIGHT);
        gutter.setStyle("-fx-padding: 6 6 0 0;");
        Runnable update = () -> {
            String text = area.getText();
            int lines = text.isEmpty() ? 1 : text.split("\n", -1).length;
            StringBuilder numbers = new StringBuilder();
            for (int i = 1; i <= lines; i++) {
                numbers.append(i).append('\n');
            }
            gutter.setText(numbers.toString());
        };
        area.textProperty().addListener((obs, o, v) -> update.run());
        area.scrollTopProperty()
                .addListener((obs, o, v) -> gutter.setTranslateY(-v.doubleValue()));
        update.run();
        return gutter;
    }

    /**
     * Shows the information window for the given entries without a solver (Swing opens a
     * non-modal {@code JDialog} from {@code SolverListener.showInformation}); no counterexample
     * tabs are added.
     *
     * @param owner the owner window; may be {@code null}
     * @param title the window title
     * @param information the tabs to show
     */
    public static void show(Window owner, String title, List<Information> information) {
        show(owner, null, title, information);
    }

    /**
     * Shows the information window for the given entries and solver (the counterexample tabs are
     * added for the Z3 CE solver with a model).
     *
     * @param owner the owner window; may be {@code null}
     * @param solver the solver whose run is presented; may be {@code null}
     * @param title the window title
     * @param information the tabs to show
     */
    public static void show(Window owner, SMTSolver solver, String title,
            List<Information> information) {
        new InformationWindowF(owner, solver, title, information).show();
    }
}
