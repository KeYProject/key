package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;

import javax.swing.AbstractAction;
import javax.swing.JFileChooser;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofScriptWorker;

@SuppressWarnings("serial")
public class ProofScriptAction extends AbstractAction {

    private final KeYMediator mediator;

    public ProofScriptAction(KeYMediator mediator) {
        super("Run proof script ...");
        this.mediator = mediator;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        try {
            MainWindow mainWindow = MainWindow.getInstance();

            final File dir = new File(mainWindow.getRecentFiles()
                    .getMostRecent().getAbsolutePath()).getParentFile();

            JFileChooser fc = new JFileChooser(dir);
            int res = fc.showOpenDialog(MainWindow.getInstance());
            if(res == JFileChooser.APPROVE_OPTION) {
                ProofScriptWorker psw = new ProofScriptWorker(mediator, fc.getSelectedFile());
                psw.init();
                psw.execute();
            }
        } catch (Exception ex) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), ex);
        }
    }

}
