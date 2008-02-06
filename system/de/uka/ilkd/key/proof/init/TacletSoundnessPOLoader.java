// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.io.File;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

/**
 * Loader for the generation of taclet proof obligations, mostly copied from
 * <code>ProblemLoader</code>
 */
public class TacletSoundnessPOLoader implements Runnable {
    final File file;
    final Main main;
    final KeYMediator mediator;
    
    private SwingWorker worker;

    ProblemInitializer init;

    
    public TacletSoundnessPOLoader(File file, Main main) {
       this.main = main;
       mediator  = main.mediator();
       this.file = file;
    }

    
    public void run () {
        /*
         * Invoking start() on the SwingWorker causes a new Thread to be created
         * that will call construct(), and then finished(). Note that finished()
         * is called even if the worker is interrupted because we catch the
         * InterruptedException in doWork().
         */
        worker = new SwingWorker () {

            public Object construct () {
                Object res = doWork ();
                return res;
            }

            public void finished () {
                mediator.startInterface ( true );
                Main main = Main.getInstance ();
                String msg = (String)get ();
                if ( !"".equals ( msg ) ) {
                    JOptionPane.showMessageDialog
                        ( main,
                          msg,
                          "Error occurred while creating proof obligation",
                          JOptionPane.ERROR_MESSAGE );
                } 
            }
        };
        
        mediator.stopInterface ( true );
        worker.start ();
    }

    protected Object doWork () {
        final TacletSoundnessPO prob =
                new TacletSoundnessPO (file.getName(), file, 
				       main.getProgressMonitor());
    
        String status = "";
        try {
	    ProofEnvironment env = mediator.getSelectedProof().env();
            prob.setInitConfig(env.getInitConfig());
	    ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	    pi.startProver(env, prob);
        } catch ( Throwable e ) {
	    mediator.getExceptionHandler().reportException(e);
	    new ExceptionDialog(mediator.mainFrame(),
		        mediator.getExceptionHandler().getExceptions());
	    mediator.getExceptionHandler().clear();
            main.setStatusLine ( "Exception occurred while creating proof obligation" );
            status = e.toString ();
            e.printStackTrace ();
        } finally {
            prob.close ();
        }

        return status;
    }

}
