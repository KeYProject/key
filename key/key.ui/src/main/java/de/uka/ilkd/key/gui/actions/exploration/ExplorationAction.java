package de.uka.ilkd.key.gui.actions.exploration;

import java.awt.event.ActionEvent;
import java.io.Reader;
import java.io.StringReader;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.pp.LogicPrinter;

public class ExplorationAction extends MainWindowAction {

    private static final long serialVersionUID = -1662459714803539089L;

    public ExplorationAction(MainWindow mw){
        super(mw);
    }

    @Override
    public void actionPerformed(ActionEvent e) {}

    Term promptForTerm(MainWindow window, Term term) {
        final String initialValue = term == null
                ? ""
                : LogicPrinter.quickPrintTerm(term, getMediator().getServices());
        
        Term result = null;
        
        while (result == null) {
            String input = JOptionPane.showInputDialog(window, "Input a formula:", initialValue);
            if (input == null) return null;

            DefaultTermParser dtp = new DefaultTermParser();

            Reader reader = new StringReader(input);
            Services services = window.getMediator().getServices();
            NamespaceSet nss = window.getMediator().getServices().getNamespaces();
            AbbrevMap scm = new AbbrevMap(); //TODO where to get abbrev map?
            
            try {
                result = dtp.parse(reader, null, services, nss, scm);
                
                if (term != null && !result.sort().equals(term.sort())) {
                    JOptionPane.showMessageDialog(window,
                            "" + result + " is of sort " + result.sort()
                            + ", but we need a term of sort " + term.sort(), 
                            "Sort mismatch", JOptionPane.ERROR_MESSAGE);
                    result = null;
                }
            } catch (ParserException e) {
                JOptionPane.showMessageDialog(window, e.getMessage(), 
                        "Malformed input", JOptionPane.ERROR_MESSAGE);
            }
        }
        
        return result;
    }


}
