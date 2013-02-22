package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JCheckBoxMenuItem;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
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
        final boolean useUnicode =  ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUseUnicode();
        final boolean usePretty = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        setSelected((useUnicode && usePretty));
        NotationInfo.UNICODE_ENABLED = (useUnicode && usePretty);
        setEnabled(usePretty);
        //setSelected(NotationInfo.UNICODE_ENABLED);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
	boolean useUnicode = ((JCheckBoxMenuItem) e.getSource()).isSelected(); 
	ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().setUseUnicode(useUnicode);
	boolean usePretty = ProofIndependentSettings.DEFAULT_INSTANCE.getViewSettings().isUsePretty();
        NotationInfo.UNICODE_ENABLED = useUnicode && usePretty;
        mainWindow.makePrettyView();
    }

}
