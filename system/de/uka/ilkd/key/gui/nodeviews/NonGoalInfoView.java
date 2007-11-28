// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.Font;
import java.awt.Rectangle;

import javax.swing.JTextArea;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.plaf.TextUI;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter;
import javax.swing.text.Highlighter.HighlightPainter;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeEvent;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.logic.ListOfInteger;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.rule.export.html.HTMLFileTaclet;


public class NonGoalInfoView extends JTextArea {
    	 
    private LogicPrinter printer;	 
    private SequentPrintFilter filter;
    
    public NonGoalInfoView (Node node, KeYMediator mediator) {
	filter = new ConstraintSequentPrintFilter 
	    ( node.sequent (), 
	      mediator.getUserConstraint ().getConstraint () );
	printer = new LogicPrinter
	    (new ProgramPrinter(null), 
	     mediator.getNotationInfo(),
	     mediator.getServices());
	printer.printSequent (null, filter);
	String s = printer.toString();
	RuleApp app = node.getAppliedRuleApp();
        s += "\nNode Nr "+node.serialNr()+"\n";
        
	if ( app != null ) {
	    s = s + "\n \nUpcoming rule application: \n";
	    if (app.rule() instanceof Taclet) {
		LogicPrinter tacPrinter = new LogicPrinter 
		    (new ProgramPrinter(null),	                     
		     mediator.getNotationInfo(),
		     mediator.getServices(),
		     true);	 
		tacPrinter.printTaclet((Taclet)(app.rule()));	 
		s += tacPrinter;
	    } else {
	    	s = s + app.rule();
	    }

	    if ( app instanceof TacletApp ) {
		TacletApp tapp = (TacletApp)app;
		if ( tapp.instantiations ().getGenericSortInstantiations () !=
		     GenericSortInstantiations.EMPTY_INSTANTIATIONS ) {
		    s = s + "\n\nWith sorts:\n";
		    s = s +
			tapp.instantiations ().getGenericSortInstantiations ();
		}

		StringBuffer sb = new StringBuffer("\n\n");
                HTMLFileTaclet.writeTacletSchemaVariablesHelper(
		    sb,tapp.taclet());
		s = s + sb;
	    }
            
            s = s + "\n\nApplication justified by: ";
            s = s + mediator.getSelectedProof().env().getJustifInfo()
                                .getJustification(app, mediator.getServices())+"\n";
            
	}

/* Removed for the book version
        s = s + "\nActive statement from:\n"+
           node.getNodeInfo().getExecStatementParentClass()+":"+
           node.getNodeInfo().getExecStatementPosition()+"\n";
*/
           
        if (node.getReuseSource() != null) {
            s += "\n"+node.getReuseSource().scoringInfo();
        }

	Config.DEFAULT.addConfigChangeListener(
	    new ConfigChangeListener() {
		    public void configChanged(ConfigChangeEvent e) {
			updateUI();
		    }
		});

	updateUI();
	setText(s);

	if (app!=null) {	 
	    highlightRuleAppPosition(app);	 
	} else {	 
	    // no rule app	 
             setCaretPosition(0);	 
	}
	
	setEditable(false);
    }


    static final Highlighter.HighlightPainter RULEAPP_HIGHLIGHTER =	 
	new DefaultHighlighter	 
	.DefaultHighlightPainter(new Color(0.5f,1.0f,0.5f));	 
 	 
    static final Highlighter.HighlightPainter IF_FORMULA_HIGHLIGHTER =	 
	new DefaultHighlighter	 
	.DefaultHighlightPainter(new Color(0.8f,1.0f,0.8f));	 
 	 
 	 
    private void highlightRuleAppPosition(RuleApp app) {	 
	try {	 
	    setHighlighter ( new DefaultHighlighter () );	 

	    // Set the find highlight first and then the if highlights
	    // This seems to make cause the find one to be painted 
	    // over the if one.
 	 
	    final Range r;
	    if ( app.posInOccurrence()==null ) {
	        // rule does not have a find-part
	        r = null;
	    } else {
	        r = highlightPos ( app.posInOccurrence (), RULEAPP_HIGHLIGHTER );
	    }

	    if ( app instanceof TacletApp ) {	 
		highlightIfFormulas ( (TacletApp)app );	 
	    }	 

	    if ( r != null ) makeRangeVisible ( r );	 
	} catch(BadLocationException badLocation) {	 
	    System.err.println("NonGoalInfoView tried to "	 
			       +"highlight an area "	 
			       +"that does not exist.");	 
	    System.err.println("Exception:"+badLocation);	 
	}	 
    }	 
 	 
    /**	 
     * Ensure that the given range is visible	 
     */	 
    private void makeRangeVisible (final Range r) {	 
	setCaretPosition ( r.start () );	 
	final Runnable safeScroller = new Runnable () {	 
		public void run () {	 
		    try {	 
			final TextUI ui = getUI ();	 
			final NonGoalInfoView t = NonGoalInfoView.this;	 
			final Rectangle rect = ui.modelToView ( t, r.start () );	 
			rect.add ( ui.modelToView ( t, r.end () ) );	 
 	 
			for ( int i = 4; i >= 0; --i ) {	 
			    final Rectangle rect2 = new Rectangle ( rect );	 
			    final int border = i * 30;	 
			    rect2.add ( rect.getMinX () - border,	 
					rect.getMinY () - border );	 
			    rect2.add ( rect.getMaxX () + border,	 
					rect.getMaxY () + border );	 
			    scrollRectToVisible ( rect2 );	 
			}	 
		    } catch ( BadLocationException badLocation ) {	 
			System.err.println("NonGoalInfoView tried to "	 
					   +"make an area visible "	 
					   +"that does not exist.");	 
			System.err.println("Exception:"+badLocation);	 
		    }	 
		}	 
	    };	 
	SwingUtilities.invokeLater ( safeScroller );	 
    }	 
 	 
    /**	 
     * @param tapp The taclet app for which the if formulae	 
     * should be highlighted.	 
     * @throws BadLocationException	 
     */	 
    private void highlightIfFormulas (TacletApp tapp)	 
	throws BadLocationException {	 
	final ListOfIfFormulaInstantiation ifs = tapp.ifFormulaInstantiations ();	 
	if ( ifs == null ) return;	 
	final IteratorOfIfFormulaInstantiation it = ifs.iterator ();	 
	while ( it.hasNext () ) {	 
	    final IfFormulaInstantiation inst2 = it.next ();	 
	    if ( !( inst2 instanceof IfFormulaInstSeq ) ) continue;	 
	    final IfFormulaInstSeq inst = (IfFormulaInstSeq)inst2;	 
	    final PosInOccurrence pos =	 
		new PosInOccurrence ( inst.getConstrainedFormula (),	 
				      PosInTerm.TOP_LEVEL,	 
				      inst.inAntec () );	 
	    final Range r = highlightPos ( pos, IF_FORMULA_HIGHLIGHTER );	 
	    makeRangeVisible ( r );	 
	}	 
    }	 
 	 
    /**	 
     * @param pos   the PosInOccurrence that should be highlighted.	 
     * @param light the painter for the highlight.	 
     * @return the range of characters that was highlighted.	 
     * @throws BadLocationException	 
     */	 
    private Range highlightPos (PosInOccurrence pos,	 
				HighlightPainter light)	 
	throws BadLocationException {	 
	InitialPositionTable posTable = printer.getPositionTable ();	 
	ListOfInteger path = posTable.pathForPosition (pos, filter);	 
	Range r = posTable.rangeForPath(path);	 
	getHighlighter().addHighlight(r.start(), r.end(), light);	 
	return r;
    }

    public void updateUI() {
	super.updateUI();
	Font myFont = UIManager.getFont(Config.KEY_FONT_INNER_NODE_VIEW);
	if (myFont != null) {
	    setFont(myFont);
	} else {
	    Debug.out("KEY-INNER_NODE_FONT not available, use standard font.");
	}
    }
}
