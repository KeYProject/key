package de.uka.ilkd.key.gui;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.util.pp.Backend;

/**
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 * Some parts of the Pretty-printing may be specific to the Swing GUI and not
 * relevant to other User Interfaces. Everything that falls into this category
 * can be declared here.
 */
public class GUILogicPrinter extends LogicPrinter {

    public GUILogicPrinter(ProgramPrinter prgPrinter, NotationInfo notationInfo, Services services, boolean purePrint) {
        super(prgPrinter, notationInfo, services, purePrint);
    }

    public GUILogicPrinter(ProgramPrinter prgPrinter, NotationInfo notationInfo, Services services) {
        super(prgPrinter, notationInfo, services);
    }

    public GUILogicPrinter(ProgramPrinter prgPrinter, NotationInfo notationInfo, Backend backend, Services services, boolean purePrint) {
        super(prgPrinter, notationInfo, backend, services, purePrint);
    }

    @Override
    public boolean hideAllTermLabels() {
        return MainWindow.getInstance().termLabelMenu.hideAllTermLabels.isSelected();
    }

}
