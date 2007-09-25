// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.gui;


import javax.swing.JOptionPane;

import de.uka.ilkd.asmkey.unit.UnitManager;
import de.uka.ilkd.asmkey.util.AsmKeYResourceManager;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.SwingWorker;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.pp.PresentationFeatures;
import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.ProofInputException;



/** Class for loading and putting in place the (partial) proof
 * of a proposition/taclet. As in asmkey, all the files are
 * already loaded and parsed, the ProblemLoader consists only
 * of preparing the necessary environment with the help
 * of the {@link UnitManager}.
 *
 * It is a SwingWorker and will do its works independently of
 * the gui-event loop.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */

public class ProblemLoader extends SwingWorker {

    /** The prover window, as reference. */
    private final ProverFrame proverFrame;

    /** The main window, as reference */
    private final Main main;
    
    /** The mediator used for loading proofs. */
    private final KeYMediator mediator;

    /** The AsmKeYResourceManager, as reference. */
    private AsmKeYResourceManager manager;

    private UnitManager unitManager;

    private ProofAggregate pl = null;
    private IteratorOfNode children = null;
    private Name prop;
    
    ProblemLoader(Name prop, Main main, ProverFrame proverFrame, UnitManager unitManager) {
	this.main = main;
	this.proverFrame = proverFrame;
	this.mediator = proverFrame.mediator();
	this.manager = AsmKeYResourceManager.getInstance();
	this.prop = prop;
	this.unitManager = unitManager;
    }
    
    public Object construct() {
	try{
	    proverFrame.setStatusLine("Loading problem");
	    pl = unitManager.prepareProof(prop, proverFrame);
	    proverFrame.setStandardStatusLine();
	    return null;
        } catch (Exception e) {
            return e;
        }
    }

    public void finished() {
	/* - rethink start and stop interface -  */
	mediator.startInterface(true);
	Exception e = (Exception) get();
	if (e == null && pl == null) {
	    e = new ProofInputException("FATAL:The ProofAggregate is null.");
	}
	if (e == null) {
	    PresentationFeatures.initialize(mediator.func_ns(),
					    mediator.getNotationInfo(),
					    mediator.getSelectedProof());
	} else {
	    e.printStackTrace();
	    //do some "clean" work.
	    JOptionPane.showMessageDialog(main, e.toString(), "Load Error",
					  JOptionPane.ERROR_MESSAGE);

	} 
    }




}
