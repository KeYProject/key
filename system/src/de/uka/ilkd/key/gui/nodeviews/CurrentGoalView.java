// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.gui.nodeviews;


import java.awt.*;
import java.awt.dnd.Autoscroll;
import java.awt.dnd.DnDConstants;
import java.awt.dnd.DragSource;
import java.awt.dnd.DropTarget;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.pp.IdentitySequentPrintFilter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.Debug;
import java.util.Vector;

/** 
 * This sequent view displays the sequent of an open goal and allows selection of
 * formulas as well as the application of rules. It offers services for highlighting 
 * formulas, selecting applicable rules (in particular taclets) and drag'n drop
 * instantiation of taclets.
 */
public class CurrentGoalView extends SequentView implements Autoscroll {

    public static final Color DEFAULT_HIGHLIGHT_COLOR = new Color(70, 100, 170, 76);

    public static final Color ADDITIONAL_HIGHLIGHT_COLOR = new Color(0, 0, 0, 38);

    public static final Color UPDATE_HIGHLIGHT_COLOR = new Color(0, 150, 130, 38);

    public static final Color DND_HIGHLIGHT_COLOR = new Color(0, 150, 130, 104);

    // the mediator
    private KeYMediator mediator;

    // the mouse/mouseMotion listener
    protected SequentViewListener listener;
    
    // an object that detects opening and closing of an Taclet instantiation dialog
    private GUIListener guiListener;
    
    // enables this component to be a Drag Source
    DragSource dragSource = null;

    private static final Insets autoScrollSensitiveRegion = new Insets(20,20,20,20);
    private final Vector<Object> updateHighlights;
    
        
    /** 
     * creates a viewer for a sequent 
     * @param mediator the KeYMediator allowing access to the
     *  current system status
     */
    public CurrentGoalView(KeYMediator mediator, MainWindow mainWindow) {
        super(mainWindow);
	setMediator(mediator);
        setBackground(Color.white);
	// disables selection
	setSelectionColor(getBackground());
	listener = new SequentViewListener(this, getMediator());
	
	guiListener = new GUIListener(){
		/** invoked if a frame that wants modal access is opened */
		public void modalDialogOpened(GUIEvent e){
		 
		    // enable textual DnD in case that the opened model dialog
		    // is the ApplyTacletDialog
		    final boolean enableDnD = e.getSource() instanceof ApplyTacletDialog;
		    listener.setModalDragNDropEnabled(enableDnD);
		    refreshHighlightning = enableDnD;
                    
                    // disable drag and drop instantiation of taclets
                    getDropTarget().setActive(false);
		}
		
		/** invoked if a frame that wants modal access is closed */
		public void modalDialogClosed(GUIEvent e){
		    if (e.getSource() instanceof ApplyTacletDialog){
			// disable drag'n'drop ...
			listener.setModalDragNDropEnabled(false);
		    } 

		    refreshHighlightning = true;
		    
                    
		    // enable drag and drop instantiation of taclets
                    getDropTarget().setActive(true);
		}
		
		/** invoked if the user wants to abort the proving session */
		public void shutDown(GUIEvent e){
		}	
	    };
		 
	addMouseListener(listener);
	addMouseMotionListener(listener);	

	// and here comes the drag'n'drop stuff that allows the user to copy
	// the currently highlighted subterm/formula by mere drag'n'dop actions
	
	dragSource = new DragSource();
	dragSource.createDefaultDragGestureRecognizer( this, 
						       DnDConstants.ACTION_COPY,
						       listener.getDragGestureListener() );

	// And now the Drag'n'drop stuff ...
	       
        final DragNDropInstantiator dragNDropInstantiator = new DragNDropInstantiator(this);
        final DropTarget aDropTarget =  
	    new DropTarget(this, 
                    dragNDropInstantiator);

        this.setAutoscrolls(true);
	this.setDropTarget(aDropTarget);
                
        
	// add listener to KeY GUI events
        getMediator().addGUIListener(guiListener);
        
        updateHighlights = new Vector<Object>();

    }
    
     /**
     * updates all updateHighlights. Firstly removes all displayed ones and
     * then gets a new list of updates to highlight
     */
    public void updateUpdateHighlights() {
        if (printer == null) return;
        
        for (Object updateHighlight : updateHighlights) {
            removeHighlight(updateHighlight);
        }

        updateHighlights.clear();
        Range[] ranges = printer.getPositionTable().getUpdateRanges();

        if (ranges != null) {
            for (Range range : ranges) {
                Object tag = getColorHighlight(UPDATE_HIGHLIGHT_COLOR);
                updateHighlights.addElement(tag);
                paintHighlight(range, tag);
            }
        }
    }
    
    protected DragSource getDragSource() {
	return dragSource;
    }

    /** sets the text being printed */
    public synchronized void printSequent() {
        if (SwingUtilities.isEventDispatchThread()) {
            printSequentImmediately();
        } else {
            Runnable sequentUpdater = new Runnable() {
                public void run() {
                    printSequentImmediately();
                }
            };
            SwingUtilities.invokeLater(sequentUpdater);
        }
    }

    /** sets the text being printed */
    public synchronized void printSequentImmediately() {
	removeMouseMotionListener(listener);
	removeMouseListener(listener);
        
        setLineWidth(computeLineWidth());
        
        if (printer != null) {
            printer.update(filter, getLineWidth());
	    boolean errorocc;
	    do {
	        errorocc = false;
	        try {
		    setText(printer.toString());
			MainWindow.getInstance().sequentSearchBar.search();
	        } catch (Error e) {
		    System.err.println("Error occurred while printing Sequent!");
		    errorocc = true;
	        }
	    } while (errorocc);
        }
        
        updateUpdateHighlights();
	restorePosition();
        addMouseMotionListener(listener);
	addMouseListener(listener);        
	repaint();
    }
    
    // last highlighted caret position
    private int lastHighlightedCaretPos;
    
    @Override
    public void highlight(Point p) {
        super.highlight(p);
        lastHighlightedCaretPos = correctedViewToModel(p);
    }
    
    /** makes the last caret position visible (if possible) */
    public void restorePosition() {
	int lastHighlightedCaretPosTmp = lastHighlightedCaretPos;
        if (!(lastHighlightedCaretPosTmp < 0 || getDocument() == null || 
	      lastHighlightedCaretPosTmp > getDocument().getLength())) {
	    setCaretPosition(lastHighlightedCaretPosTmp);
	}
    }
    
    /** sets the LogicPrinter to use in case there is no proof available.
     * @param sp the LogicPrinter that is used
     */
    public void setPrinterNoProof() {
    	printer = new LogicPrinter(new ProgramPrinter(null), null, null);
    }
    
    /** sets the LogicPrinter to use
     * @param sp the LogicPrinter that is used
     * @param f the SequentPrintFilter that is used
     */
    public void setPrinter(Goal goal) {
        filter = new IdentitySequentPrintFilter(goal.sequent());
        printer = new LogicPrinter(new ProgramPrinter(null),
                getMediator().getNotationInfo(),
                mediator.getServices());
    }

    protected SequentPrintFilter getSequentPrintFilter() {
    	return filter;
    }

    /** return used LogicPrinter
     * @return the LogicPrinter that is used
     */
    public LogicPrinter getPrinter() {
    	return printer;
    }

    /** sets the mediator
     * @param mediator the KeYMediator used to communicate with other
     * components 
     */
    private void setMediator(KeYMediator mediator) {
        Debug.assertTrue(mediator != null, "Mediator must be set");
        this.mediator = mediator;
    }

    /** returns the mediator of this view
     * @return the KeYMediator
     */
    public KeYMediator getMediator() {
	return mediator;
    }

    /** selected rule to apply 
     * @param taclet the selected Taclet
     * @param pos the PosInSequent describes the position where to apply the 
     * rule 
     */
    void selectedTaclet(TacletApp taclet, PosInSequent pos) {
    	getMediator().selectedTaclet(taclet, pos);
    }

    /**
     * Enables drag'n'drop of highlighted subterms in the sequent window.
     * @param allowDragNDrop enables drag'n'drop iff set to true.
     */
    public synchronized void setModalDragNDropEnabled(boolean allowDragNDrop){
	    listener.setModalDragNDropEnabled(allowDragNDrop);
	}
    
    /**
     * Checks whether drag'n'drop of highlighted subterms in the sequent window
     * currently is enabled..
     * @return true iff drag'n'drop is enabled.
     */	
    public synchronized boolean modalDragNDropEnabled(){
	return listener.modalDragNDropEnabled();
    }

    public String getHighlightedText() {
       return getHighlightedText(getPosInSequent(getMousePosition()));
    }
	
    public PosInSequent getMousePosInSequent() {
       return getPosInSequent(getMousePosition());
    }
    
    /**
     * used for autoscrolling when performing drag and drop actions.
     * Computes the rectangle to be made visible. 
     */
    public void autoscroll(Point loc) {       
        final Insets insets = getAutoscrollInsets();
        final Rectangle outer = getVisibleRect();
        final Rectangle inner = new Rectangle(outer.x+insets.left, 
                outer.y+insets.top, 
                outer.width-(insets.left+insets.right), 
                outer.height-(insets.top+insets.bottom));
        
        if (!inner.contains(loc))  {
            Rectangle scrollRect = new Rectangle(loc.x-insets.left, 
                    loc.y-insets.top, insets.left+insets.right, 
                    insets.top+insets.bottom);            
            scrollRectToVisible(scrollRect);
        }
    }

    /**
     * used to define the area in which autoscrolling will be
     * initialized
     */
    public Insets getAutoscrollInsets() {      
        return autoScrollSensitiveRegion;
    }

    public String getTitle() {
        return "Current Goal";
    }

}
