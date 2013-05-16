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
import java.awt.event.ComponentEvent;
import java.awt.event.ComponentListener;
import java.awt.event.HierarchyBoundsListener;
import java.awt.event.HierarchyEvent;
import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import javax.swing.SwingUtilities;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.gui.configuration.Config;
import de.uka.ilkd.key.gui.configuration.ConfigChangeAdapter;
import de.uka.ilkd.key.gui.configuration.ConfigChangeListener;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.pp.Range;
import de.uka.ilkd.key.pp.SequentPrintFilter;
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

    // the current line width
    int lineWidth;
    
    // the used sequent
    private Sequent seq;

    // the mediator
    private KeYMediator mediator;

    // the mouse/mouseMotion listener
    protected SequentViewListener listener;
    
    // a component and property change listener used to
    // update the sequent view on font or size changes
    private SeqViewChangeListener changeListener;
    
    // an object that detects opening and closing of an Taclet instantiation dialog
    private GUIListener guiListener;

    private ConfigChangeListener configChangeListener = new ConfigChangeAdapter(this);
    
    // enables this component to be a Drag Source
    DragSource dragSource = null;

    private static final Insets autoScrollSensitiveRegion = new Insets(20,20,20,20);
    private final Vector<Object> updateHighlights;
    
        
    /** 
     * creates a viewer for a sequent 
     * @param mediator the KeYMediator allowing access to the
     *  current system status
     */
    public CurrentGoalView(KeYMediator mediator) {
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
        
        // add a listener to this component
        changeListener = new SeqViewChangeListener();
        addComponentListener(changeListener);
        addPropertyChangeListener("font", changeListener);
        addHierarchyBoundsListener(changeListener);
        updateHighlights = new Vector<Object>();

    }
    
     /**
     * updates all updateHighlights. Firstly removes all displayed ones and
     * then gets a new list of updates to highlight
     */
    public void updateUpdateHighlights() {
        if (printer == null) return;
        LogicPrinter printer = this.printer;

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
    
    @Override
    public void addNotify() {
        super.addNotify();
        Config.DEFAULT.addConfigChangeListener(configChangeListener);
        updateUI();
    }
    
    @Override
    public void removeNotify(){
        super.removeNotify();
        Config.DEFAULT.removeConfigChangeListener(configChangeListener);
    }


    @Override
    protected void finalize(){
        try{
            Config.DEFAULT.removeConfigChangeListener(configChangeListener);
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
    
    
    protected DragSource getDragSource() {
	return dragSource;
    }

    /** sets the text being printed */
    public synchronized void printSequent() {	
        if ( SwingUtilities.isEventDispatchThread () ) {
	    printSequentImmediately ();
	} else {
	    Runnable sequentUpdater = new Runnable() {
		    public void run() {
			printSequentImmediately ();
		    }
		};
	    SwingUtilities.invokeLater(sequentUpdater);
	}
    }

    /**
     * computes the line width
     */
    private int computeLineWidth() {
        // assumes we have a uniform font width
        int maxChars = (int) 
            (getVisibleRect().getWidth()/getFontMetrics(getFont()).charWidth('W'));
        
        if (maxChars > 1) maxChars-=1;    
        
        return maxChars;
    }
    

    /** sets the text being printed */
    public synchronized void printSequentImmediately() {
	removeMouseMotionListener(listener);
	removeMouseListener(listener);
        
        lineWidth = computeLineWidth();
        
        if (printer != null) {
            printer.update(seq, filter, lineWidth);
	    boolean errorocc;
	    do {
	        errorocc = false;
	        try {
		    setText(printer.toString());

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
    
    /** makes the last caret position visible (if possible) */
    public void restorePosition() {
	int lastHighlightedCaretPosTmp = lastHighlightedCaretPos;
        if (!(lastHighlightedCaretPosTmp < 0 || getDocument() == null || 
	      lastHighlightedCaretPosTmp > getDocument().getLength())) {
	    setCaretPosition(lastHighlightedCaretPosTmp);
	}
    }
    
    /** sets the LogicPrinter to use
     * @param sp the LogicPrinter that is used
     */
    public void setPrinter(LogicPrinter sp, Sequent s) {
    	setPrinter ( sp, null, s );
    }

    protected SequentPrintFilter getSequentPrintFilter() {
    	return filter;
    }

    /** sets the LogicPrinter to use
     * @param sp the LogicPrinter that is used
     * @param f the SequentPrintFilter that is used
     */
    public void setPrinter(LogicPrinter sp, SequentPrintFilter f, Sequent s) {
        printer = sp;
        filter  = f;
        seq = s;
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
    
    private class SeqViewChangeListener implements ComponentListener,
    PropertyChangeListener, HierarchyBoundsListener {
        
        
        public void componentHidden(ComponentEvent e) {}
        
        public void componentMoved(ComponentEvent e) {}
        
        public void componentResized(ComponentEvent e) {            
            // reprint sequent
            int lw = computeLineWidth();
            if (lw != lineWidth) { 
                printSequent();
            }
        }
        
        public void componentShown(ComponentEvent e) {}
        
        public void propertyChange(PropertyChangeEvent evt) {
            // reprint sequent
            printSequent();            
        }
        
        public void ancestorMoved(HierarchyEvent e) {}
        
        public void ancestorResized(HierarchyEvent e) {
            //          reprint sequent            
            int lw = computeLineWidth();
            if (lw != lineWidth) { 
                printSequent();
            }
        }
    }

    public String getTitle() {
        return "Current Goal";
    }

}
