package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.NoFindTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.Reader;
import java.io.StringReader;

/**
 * @author Alexander Weigl
 * @version 1 (24.05.18)
 */
public class AddFormulaToAntecedentAction extends MainWindowAction {

    public AddFormulaToAntecedentAction() {
        this(MainWindow.getInstance());
    }

    public AddFormulaToAntecedentAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Add formula to antecedent");
    }

    static Term promptForTerm(MainWindow window, String initialValue) {
        String input = JOptionPane.showInputDialog(window, "Input a formula:", initialValue);
        if (input == null) return null;

        DefaultTermParser dtp = new DefaultTermParser();

        Reader reader = new StringReader(input);
        Services services = window.getMediator().getServices();
        NamespaceSet nss = window.getMediator().getServices().getNamespaces();
        AbbrevMap scm = new AbbrevMap(); //TODO where to get abbrev map?
        try {
            return dtp.parse(reader, null, services, nss, scm);
        } catch (ParserException e) {
            e.printStackTrace();
            return null;
        }
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        Term t = promptForTerm(mainWindow, "");
        if (t == null) return;
        NoFindTacletBuilder builder = new NoFindTacletBuilder();
        builder.setName(new Name("add_formula_antec"));
        Semisequent semisequent = new Semisequent(new SequentFormula(t));
        Sequent addedFormula = Sequent.createAnteSequent(semisequent);
        ImmutableList<TacletGoalTemplate> templates = ImmutableSLList.nil();
        templates = templates.append(new TacletGoalTemplate(addedFormula, ImmutableSLList.nil()));
        builder.setTacletGoalTemplates(templates);
        Taclet taclet = builder.getTaclet();
        Goal g = getMediator().getSelectedGoal();
        ImmutableList<Goal> result = g.apply(NoPosTacletApp.createNoPosTacletApp(taclet));
        result.forEach(goal -> goal.node().getNodeInfo().setExploration(true));
    }
}
