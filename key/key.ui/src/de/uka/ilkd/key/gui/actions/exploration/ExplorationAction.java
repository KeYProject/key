package de.uka.ilkd.key.gui.actions.exploration;

import de.uka.ilkd.key.core.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;

import javax.swing.*;
import java.awt.event.ActionEvent;
import java.io.Reader;
import java.io.StringReader;

public class ExplorationAction extends MainWindowAction {
    public ExplorationAction(MainWindow mw){
        super(mw);
    }

    @Override
    public void actionPerformed(ActionEvent e) {}

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


}
