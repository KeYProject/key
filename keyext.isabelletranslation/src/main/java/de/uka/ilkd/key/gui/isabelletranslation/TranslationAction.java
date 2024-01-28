package de.uka.ilkd.key.gui.isabelletranslation;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.actions.MainWindowAction;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.awt.event.ActionEvent;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;

public class TranslationAction extends MainWindowAction {

    private static final Logger LOGGER = LoggerFactory.getLogger(TranslationAction.class);

    public TranslationAction(MainWindow mainWindow) {
        super(mainWindow);
        setName("Translate to Isabelle");
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        LOGGER.info("Translation Action");

        generateTranslation();
    }

    private void generateTranslation() {
        KeYMediator mediator = getMediator();
        IsabelleTranslator translator = new IsabelleTranslator(mediator.getServices());
        try {
            //TODO let user choose where to save file?
            String path = System.getProperty("user.home") + "\\Translation.thy";
            StringBuilder translation = translator.translateProblem(mediator.getSelectedGoal().sequent(), mediator.getServices());
            try {
                Files.write(Paths.get(path), translation.toString().getBytes());
                LOGGER.info("Saved to: " + path);
            } catch (IOException e) {
                //TODO handle exception
                throw new RuntimeException(e);
            }
        } catch (IllegalFormulaException e) {
            //TODO output alert to user
            throw new RuntimeException(e);
        }
    }
}
