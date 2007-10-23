// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.awt.Dimension;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;

import javax.swing.*;

import de.uka.ilkd.key.cspec.ComputeSpecification;
import de.uka.ilkd.key.gui.nodeviews.SequentView;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.util.Debug;

/**
 * This class is a facade for computing the specification of a program,
 * and displaying a corresponding view.
 *
 * @author Andr&eacute; Platzer
 * @version 1.1, 2003-02-01
 * @version-revision $Revision: 1.14.1.1.2.1.2.4.1.1 $, $Date: Tue, 26 Jun 2007 14:56:17 +0200 $
 * @see de.uka.ilkd.key.cspec.ComputeSpecification
 */
public class ComputeSpecificationView {

    private ComputeSpecificationView() {}

    private static final JRadioButtonMenuItem createRadioButton_Prestate(ButtonGroup group,
							      String label,
							      final int value) {
	JRadioButtonMenuItem menuItem =
	    new JRadioButtonMenuItem(label,
				     ComputeSpecification.getPrestateRemember() == value
				     );
	group.add(menuItem);
	menuItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    ComputeSpecification.setPrestateRemember(value);
		}});
	return menuItem;
    }
    private static final JRadioButtonMenuItem createRadioButton_Poststate(ButtonGroup group,
							      String label,
							      final int value) {
	JRadioButtonMenuItem menuItem =
	    new JRadioButtonMenuItem(label,
				     ComputeSpecification.getPoststateRemember() == value
				     );
	group.add(menuItem);
	menuItem.addActionListener(new ActionListener() {
		public void actionPerformed(ActionEvent e) {
		    ComputeSpecification.setPoststateRemember(value);
		}});
	return menuItem;
    }

    public static JMenuItem createOptionMenuItems() {
	ButtonGroup prestateRememberGroup = new ButtonGroup();
	JMenu rememberMenu = new JMenu("Specification Extraction");

	rememberMenu.add(createRadioButton_Prestate(prestateRememberGroup,
						    "Prestate Remember Equations",
						    ComputeSpecification.PRESTATE_REMEMBER_EQUATIONS));

	rememberMenu.add(createRadioButton_Prestate(prestateRememberGroup,
						    "Prestate Remember Updates",
						    ComputeSpecification.PRESTATE_REMEMBER_UPDATES));

	rememberMenu.add(createRadioButton_Prestate(prestateRememberGroup,
						    "Prestate Remember Implicit",
						    ComputeSpecification.PRESTATE_REMEMBER_IMPLICIT));


	rememberMenu.addSeparator();
	ButtonGroup poststateRememberGroup = new ButtonGroup();

	rememberMenu.add(createRadioButton_Poststate(poststateRememberGroup,
						    "Poststate Remember Equations",
						    ComputeSpecification.POSTSTATE_REMEMBER_EQUATIONS));
	rememberMenu.add(createRadioButton_Poststate(poststateRememberGroup,
						    "Poststate Remember Accumulator",
						    ComputeSpecification.POSTSTATE_REMEMBER_STATE_CHANGE_ACCUMULATION));

	return rememberMenu;
    }
    
    /**
     * A facade for the user-interface, displaying the computed
     * specification of a program.
     * @param mediator the KeY-mediator containing the specification construction proof.
     * @see de.uka.ilkd.key.casetool.FunctionalityOnModel#computeSpecification(ReprModelMethod)
     */
    public static final void show(KeYMediator mediator) {
	try{
	    final Term spec = new ComputeSpecification().computeSpecification(mediator);
	    final Sequent spec2 =
		Sequent.createSuccSequent(Semisequent.EMPTY_SEMISEQUENT
					  .insertLast(new ConstrainedFormula(spec))
					  .semisequent());
	    Debug.out("\nOverall specification is:\n", spec);
	    Debug.out("\nalias:\n", spec2);
	    final SequentView view = new SequentView(mediator);
	    view.setPreferredSize(new Dimension(800, 600));
	    view.setPrinter(new LogicPrinter(new ProgramPrinter(null), 
                                             mediator.getNotationInfo(),
                                             mediator.getServices()), spec2);
	    view.printSequent();
	    view.setCaretPosition(0); // at least until a better solution
	    final JScrollPane pane =
		new JScrollPane(view,
				JScrollPane.VERTICAL_SCROLLBAR_ALWAYS,
				JScrollPane.HORIZONTAL_SCROLLBAR_AS_NEEDED
		    );
	    
	    pane.setPreferredSize(new Dimension(600, 400));
	    mediator.popupInformationMessage(pane, "Computed Specification", false);
	} catch(Exception e) {
	   mediator.getExceptionHandler().reportException(e);
	   new ExceptionDialog(mediator.mainFrame(), 
                  mediator.getExceptionHandler().getExceptions());
	   mediator.getExceptionHandler().clear();
	}
    }

}// ComputeSpecificationView
