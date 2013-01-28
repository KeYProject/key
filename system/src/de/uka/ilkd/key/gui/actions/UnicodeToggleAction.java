package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.util.UnicodeHelper;

@SuppressWarnings("serial")
public class UnicodeToggleAction extends MainWindowAction {

    public UnicodeToggleAction(MainWindow window) {
        super(window);
        setName("Use Unicode symbols");
        setTooltip("If checked formulae are displayed with special Unicode characters" +
            " (such as \""+UnicodeHelper.AND+"\") instead of the traditional ASCII ones. \n"+
            "Only works in combination with pretty printing (see above).");
        setSelected(NotationInfo.UNICODE_ENABLED);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        NotationInfo.UNICODE_ENABLED = ((JCheckBoxMenuItem) e.getSource()).isSelected();
        mainWindow.makePrettyView();
    }

}
