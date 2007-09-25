// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.gui;


import java.awt.event.*;
import java.io.File;

import javax.swing.JMenu;
import javax.swing.JMenuBar;
import javax.swing.JMenuItem;
import javax.swing.KeyStroke;

import de.uka.ilkd.asmkey.proof.AsmProof;
import de.uka.ilkd.asmkey.unit.UnitException;
import de.uka.ilkd.asmkey.unit.UnitManager;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.rule.ListOfBuiltInRule;



/** This is the main class for starting the standalone prover of
 * ASM-KeY. The class extends the default Main class of the core
 * system.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public final class ProverFrame extends de.uka.ilkd.key.gui.Main {

    private Main main;

    protected ProverFrame(String title) {
       super(title);
	//HACK: we set our own simplifier.
	//mediator.setSimplifier(new de.uka.ilkd.asmkey.logic.SimultaneousUpdateSimplifier());
       WindowListener[] wls = getWindowListeners();
       // HACK: we would like the following:
       /*for (int i =0; i<wls.length; i++) {
	   if (wls[i] instanceof de.uka.ilkd.key.gui.Main.MainListener) {
	       removeWindowListener(wls[i]);
	   }
	   }*/
       removeWindowListener(wls[0]);
       addWindowListener(new ProverFrameListener());
    }

    public static de.uka.ilkd.key.gui.Main getInstance() {
        if (instance == null) instance = 
            new ProverFrame("ASMKeY -- Prover");
        if (!instance.isVisible()) instance.setVisible(true);
        return instance;
    }

    void setMain(Main main) {
	this.main = main;
    }

    public Main main() {
	return main;
    }
    
    protected void layoutMain() {
	/* first we do the main layout
	 * to get the standart key-layout.
	 */
	super.layoutMain();
	

	/* asmkey needs a different gui. we must
	 * modify the main layout and the menu
	 * to suit our needs.
	 */
	
	rebuildMenuBar();

    }

    

    /* Overwrite method from super class. */
    protected void loadProblem(File file) {
	// TO SEE HOW TO DO IT. recentFiles.addRecentFile(file.getAbsolutePath());
	setStatusLine("Loading problem from " + file.getName());
        //(new ProblemLoader(file, this)).run();
	setStandardStatusLine();
	
    }


    private void rebuildMenuBar() {
	JMenuBar menubar = getJMenuBar();
	JMenu viewMenu, proofMenu;
	JMenuItem save;
	
	// We do not need a file menu
	menubar.remove(0);
	viewMenu = menubar.getMenu(0);
	proofMenu = menubar.getMenu(1);
	menubar.remove(viewMenu);
	menubar.remove(proofMenu);
	menubar.add(viewMenu,0);
	menubar.add(proofMenu,0);
	

	// We add a 'save proof' menu item in the 'proof menu'
	// after the 'abandon task' menu item.

	save = new JMenuItem("Save proof");
	save.setAccelerator(KeyStroke.getKeyStroke
			    (KeyEvent.VK_S, ActionEvent.CTRL_MASK));
	save.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    saveProof();
		}});
	proofMenu.insert(save, 2);

    }
    

    protected void saveProof() {
	UnitManager manager = main().unitManager();
	try {
	    manager.saveProof((AsmProof)mediator.getProof());
	} catch (ClassCastException e) {
	    mediator.notify(new GeneralFailureEvent
			    ("The Proof should be an AsmProof in AsmKey: " +
			     e.getMessage()));
	} catch (UnitException e) {
	    mediator.notify(new GeneralFailureEvent(e.getMessage()));
	}
    }
   

    private LemmaMenu lemmaMenu;

    public void buildLemmaMenu(ListOfBuiltInRule lemmaRules) {
	JMenuBar menubar = getJMenuBar();

	/* remove the old Lemma Menu */
	if(lemmaMenu != null) {
	    menubar.remove(lemmaMenu);
	}

	lemmaMenu = new LemmaMenu(mediator, lemmaRules);
	menubar.add(lemmaMenu, menubar.getMenuCount()-2);
	
    }

    class ProverFrameListener extends WindowAdapter {
	public void windowClosing(WindowEvent e) {
	    closeTask();	    
	}
    } 

}
