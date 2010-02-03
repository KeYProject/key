// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
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

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;

/**
 * Loader for the generation of taclet proof obligations, mostly copied from
 * <code>ProblemLoader</code>
 */
public class TacletSoundnessPOLoader implements Runnable {
    private final File file;
    private final IMain main;
    private final KeYMediator mediator;
    
    private SwingWorker worker;

    private final ListOfGoal openGoals;

    
    public TacletSoundnessPOLoader(File file, IMain main, ListOfGoal openGoals) {
       this.main = main;
       mediator  = main.mediator();
       this.file = file;
       this.openGoals = openGoals;
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
                String msg = (String)get ();
                if ( !"".equals ( msg ) ) {
                    JOptionPane.showMessageDialog
                        ( mediator.mainFrame(),
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
				       main.getProgressMonitor(),
                                       openGoals);
    
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
