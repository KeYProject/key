package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import de.uka.ilkd.key.smt.IllegalFormulaException;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class TranslationAction extends MainWindowAction {
    public TranslationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        System.out.println("Translation Action");

        generateTranslation();
    }

    private void generateTranslation() {
        IsabelleTranslator translator = new IsabelleTranslator();
        KeYMediator mediator = getMediator();
        try {
            //TODO let user choose where to save file?
            String path = "Translation.thy";
            StringBuilder translation = translator.translateProblem(mediator.getSelectedGoal().sequent(), mediator.getServices());

            try {
                Files.write(Paths.get(path), translation.toString().getBytes());
            } catch (IOException e) {
                throw new RuntimeException(e);
            }
        } catch (IllegalFormulaException e) {
            throw new RuntimeException(e);
        }
    }
}
