package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Use this class in case no proof is loaded.
 *
 * @author Kai Wallisch
 */
public class EmptySequent extends SequentView {

    private static final long serialVersionUID = 7572244482555772604L;

    public EmptySequent(MainWindow mainWindow) {
        super(mainWindow);
        setBackground(INACTIVE_BACKGROUND_COLOR);
    }

    @Override
    public String getTitle() {
        return "No proof loaded";
    }

    @Override
    public void printSequent() {
    }

}
