/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.smt;

import java.awt.*;
import java.util.Collection;
import javax.swing.*;

import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.sourceview.TextLineNumber;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;


/**
 * The information window is used to present detailed information about the execution of a solver.
 * In particular it presents information about: - the concrete translation that was passed to the
 * solver - the translation of the taclets - the messages that were sent between KeY and the
 * external solvers.
 */
public class InformationWindow extends JDialog {

    private static final long serialVersionUID = 1L;

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


    public static class Information {
        private final String content;
        private final String title;
        private final String solver;

        public Information(String title, String content, String solver) {
            super();
            this.content = content;
            this.title = title;
            this.solver = solver;
        }

        public String getContent() {
            return content;
        }

        public String getTitle() {
            return title;
        }

        public String getSolver() {
            return solver;
        }
    }

    private JTabbedPane tabbedPane;
    private Model model;

    public InformationWindow(Dialog parent, SMTSolver solver, Collection<Information> information,
            String title) {
        super(parent);
        this.setTitle(title);
        initModel(solver);
        for (Information el : information) {
            getTabbedPane().addTab(el.title, newTab(el));
        }

        setSize(600, 500);
        this.getContentPane().add(getTabbedPane());
        this.setModalExclusionType(ModalExclusionType.APPLICATION_EXCLUDE);
        this.setDefaultCloseOperation(DISPOSE_ON_CLOSE);
        this.setLocationRelativeTo(parent);
        this.setVisible(true);
    }

    private void initModel(SMTSolver solver) {
        if (solver.getType() != SolverTypes.Z3_CE_SOLVER) {
            return;
        }
        if (solver.getSocket().getQuery() == null) {
            return;
        }

        Model m = solver.getSocket().getQuery().getModel();
        this.model = m;
        this.setTitle("Counterexample " + this.getTitle());
        getTabbedPane().addTab("Counterexample", createModelTab());
        createHelpTab();
    }

    private void createHelpTab() {
        final JTextArea content = new JTextArea();
        content.setEditable(false);
        content.setText(CE_HELP);
        JScrollPane pane = new JScrollPane();
        pane.getViewport().add(content);
        pane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);
        getTabbedPane().addTab("Help", pane);
    }

    private Component createModelTab() {

        CETree tree = new CETree(model);
        JScrollPane pane = new JScrollPane();
        pane.getViewport().add(tree.getTreeComponent());
        pane.setVerticalScrollBarPolicy(JScrollPane.VERTICAL_SCROLLBAR_ALWAYS);

        return pane;

    }

    private Component newTab(Information information) {
        final JTextPane content = new JTextPane();
        Font font = UIManager.getFont(Config.KEY_FONT_SEQUENT_VIEW);
        content.setFont(font);
        content.setEditable(false);
        content.setText(information.content);

        JPanel nowrap = new JPanel(new BorderLayout());
        nowrap.add(content);
        JScrollPane scrPreview = new JScrollPane();
        scrPreview.setViewportView(nowrap);

        TextLineNumber lineNumbers = new TextLineNumber(content, 1);
        scrPreview.setRowHeaderView(lineNumbers);

        return scrPreview;
    }


    private JTabbedPane getTabbedPane() {
        if (tabbedPane == null) {
            tabbedPane = new JTabbedPane();
        }
        return tabbedPane;
    }


}
