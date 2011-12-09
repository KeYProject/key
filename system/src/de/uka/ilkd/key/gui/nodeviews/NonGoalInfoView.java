// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
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
import java.util.Iterator;

import javax.swing.JTextArea;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.plaf.TextUI;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.Highlighter;
import javax.swing.text.Highlighter.HighlightPainter;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeAdapter;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.pp.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.GenericSortInstantiations;
import de.uka.ilkd.key.util.Debug;


public class NonGoalInfoView extends JTextArea {
    	 
    /**
     * 
     */
    private static final long serialVersionUID = -868094158643337989L;
    private LogicPrinter printer;	 
    private SequentPrintFilter filter;
    private InitialPositionTable posTable;
    private ConfigChangeListener configChangeListener 
    	= new ConfigChangeAdapter(this);
    
    
    private static void writeSVModifiers(StringBuffer out, SchemaVariable sv) {        
        boolean started = false;        
        if (sv.isRigid() && !(sv instanceof VariableSV)) {
            if (!started) out.append("[");
            out.append("rigid");
            started = true;
        }        
        if (sv instanceof ProgramSV && ((ProgramSV)sv).isListSV()) {
            if (!started) out.append("[");
            else {
                out.append(", ");
            }
            out.append("list");
            started = true;
        }        
        
        if (started) out.append("]");        
    }
    
    
    private static void writeTacletSchemaVariable(StringBuffer out, 
	    					  SchemaVariable schemaVar) {
	if(schemaVar instanceof ModalOperatorSV) {            
	    final ModalOperatorSV modalOpSV = (ModalOperatorSV)schemaVar;	    
	    String sep = "";
	    for (final Operator op : modalOpSV.getModalities()) {
		out.append ( sep );
		out.append ( op.name() );
		sep = ", ";
	    }
	    out.append(" } " + modalOpSV.name());
	} else if(schemaVar instanceof TermSV) {
	    out.append ("\\term");
	} else if(schemaVar instanceof FormulaSV) {
	    out.append ("\\formula");
	} else if(schemaVar instanceof UpdateSV) {
	    out.append("\\update");
	} else if(schemaVar instanceof ProgramSV) {
	    out.append ("\\program");
	} else if(schemaVar instanceof VariableSV) {
	    out.append ("\\variables");
	} else if(schemaVar instanceof SkolemTermSV) {
	    out.append ("\\skolemTerm");
	} else {
	    out.append ("?");
	}                       
	writeSVModifiers(out, schemaVar);
	if(!(schemaVar instanceof FormulaSV || schemaVar instanceof UpdateSV)) {
	    out.append(" " + schemaVar.sort().declarationString());
	}
	out.append(  " " + schemaVar.name() );
    }
    
    
    public static void writeTacletSchemaVariablesHelper(StringBuffer out, 
                                                        final Taclet t) {
	ImmutableSet<SchemaVariable> schemaVars = t.getIfFindVariables();
        ImmutableList<NewVarcond> lnew = t.varsNew();
	while (!lnew.isEmpty()) {
	    schemaVars = schemaVars.add(lnew.head().getSchemaVariable());
	    lnew = lnew.tail();
	}
	Iterator<NewDependingOn> newDepIt = t.varsNewDependingOn();
	while (newDepIt.hasNext()) {
	    schemaVars = schemaVars.add(newDepIt.next().first());
	}	

        if (schemaVars.size() > 0)
        {
            out.append ( "\\schemaVariables {\n" );
            for (SchemaVariable schemaVar1 : schemaVars) {
                final SchemaVariable schemaVar = schemaVar1;
                // write indentation
                out.append("  ");
                // write declaration
                writeTacletSchemaVariable(out, schemaVar);
                // write newline
                out.append(";\n");
            }
            out.append ( "}\n" );
        }
    }    
    
    
    public NonGoalInfoView (Node node, KeYMediator mediator) {
	filter = new IdentitySequentPrintFilter( node.sequent () );
	printer = new LogicPrinter
	    (new ProgramPrinter(null), 
	     mediator.getNotationInfo(),
	     mediator.getServices());
	printer.printSequent (null, filter);
	String s = printer.toString();
        posTable = printer.getPositionTable();
        printer=null;
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
                writeTacletSchemaVariablesHelper(sb,tapp.taclet());
		s = s + sb;
	    }
            
//            s = s + "\n\nApplication justified by: ";
//            s = s + mediator.getSelectedProof().env().getJustifInfo()
//                                .getJustification(app, mediator.getServices())+"\n";            
	}

           
	Config.DEFAULT.addConfigChangeListener(configChangeListener);

	updateUI();
	setText(s);

	if (app != null) {	 
	    highlightRuleAppPosition(app);	 
	} else {	 
	    // no rule app	 
	    setCaretPosition(0);	 
	}
	
	setEditable(false);
    }
    
    
    public void addNotify() {
        super.addNotify();
        Config.DEFAULT.addConfigChangeListener(configChangeListener);
    }
    
    
    public void removeNotify(){
        super.removeNotify();
        unregisterListener();
    }

    
    public void unregisterListener(){
        if(configChangeListener!=null){
            Config.DEFAULT.removeConfigChangeListener(configChangeListener);            
        }
    }
    
    
    protected void finalize(){
        try{
            unregisterListener();
        } catch (Throwable e) {
            MainWindow.getInstance().notify(new GeneralFailureEvent(e.getMessage()));
        }finally{
                try {
                    super.finalize();
                } catch (Throwable e) {
                    MainWindow.getInstance().notify(new GeneralFailureEvent(e.getMessage()));
                }
        }
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
	    } else if(app instanceof BuiltInRuleApp) {
		highlightIfInsts ( (BuiltInRuleApp)app );	 		
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
			if(ui == null)
			    return;
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
	final ImmutableList<IfFormulaInstantiation> ifs = tapp.ifFormulaInstantiations ();	 
	if ( ifs == null ) return;
        for (final IfFormulaInstantiation inst2 : ifs) {
            if (!(inst2 instanceof IfFormulaInstSeq)) continue;
            final IfFormulaInstSeq inst = (IfFormulaInstSeq) inst2;
            final PosInOccurrence pos =
                    new PosInOccurrence(inst.getConstrainedFormula(),
                            PosInTerm.TOP_LEVEL,
                            inst.inAntec());
            final Range r = highlightPos(pos, IF_FORMULA_HIGHLIGHTER);
            makeRangeVisible(r);
        }
    }	 
    
    
    private void highlightIfInsts(BuiltInRuleApp bapp) 
    		throws BadLocationException {
	final ImmutableList<PosInOccurrence> ifs = bapp.ifInsts();
	for(PosInOccurrence pio : ifs) {
	    final Range r = highlightPos ( pio, IF_FORMULA_HIGHLIGHTER );	 
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
	ImmutableList<Integer> path = posTable.pathForPosition (pos, filter);	 
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
