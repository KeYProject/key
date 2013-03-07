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
import java.util.HashMap;
import java.util.Vector;

import javax.swing.JEditorPane;
import javax.swing.SwingUtilities;
import javax.swing.UIManager;
import javax.swing.text.BadLocationException;
import javax.swing.text.DefaultHighlighter;
import javax.swing.text.DefaultHighlighter.DefaultHighlightPainter;
import javax.swing.text.Highlighter.HighlightPainter;

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

/** 
 * This sequent view displays the sequent of an open goal and allows selection of
 * formulas as well as the application of rules. It offers services for highlighting 
 * formulas, selecting applicable rules (in particular taclets) and drag'n drop
 * instantiation of taclets.
 */
public class LeafNodeView extends SequentView implements Autoscroll {

    public static final Color DEFAULT_HIGHLIGHT_COLOR = new Color(70, 100, 170, 76);

    public static final Color ADDITIONAL_HIGHLIGHT_COLOR = new Color(0, 0, 0, 38);

    public static final Color UPDATE_HIGHLIGHT_COLOR = new Color(0, 150, 130, 38);

    public static final Color DND_HIGHLIGHT_COLOR = new Color(0, 150, 130, 104);

    public static final Color BACKGROUND_COLOR = new Color(249, 249, 249);

    // the used sequentprinter
    public LogicPrinter printer;
    
    // the default tag of the highlight
    private Object defaultHighlight;

    // the current tag of the highlight
    private Object currentHighlight;

    // an additional highlight to mark the first active statement
    private Object additionalHighlight;

    // the used sequent filter
    private SequentPrintFilter filter;

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

    // last highlighted caret position
    private int lastHighlightedCaretPos;

    private static final Insets autoScrollSensitiveRegion = new Insets(20,20,20,20);
    
        
    /** 
     * creates a viewer for a sequent 
     * @param mediator the KeYMediator allowing access to the
     *  current system status
     */
    public LeafNodeView(KeYMediator mediator) {
	setMediator(mediator);
        // set background color
        setBackground(BACKGROUND_COLOR);
	// disables selection
	setSelectionColor(getBackground());
	// sets the painter for the highlightning
	setHighlighter(new DefaultHighlighter());
	//sets initial highlight (not visible) and stores its tag

        // REMARK: THE ORDER FOR ADDING HIGHLIGHTS IS CRUCIAL
	// WHEN USING OVERLAPPING HIGHLIGHTS:
	// Adding highlight H1 before highlight H2 ensures that 
	// H1 can overwrite overlapping parts of H2 !!!
        	        
	additionalHighlight = getColorHighlight(ADDITIONAL_HIGHLIGHT_COLOR);
	defaultHighlight = getColorHighlight(DEFAULT_HIGHLIGHT_COLOR);
	currentHighlight = defaultHighlight;
		
        setSequentViewFont();

	listener = new SequentViewListener(this, mediator());
	
	guiListener = new GUIListener(){
		/** invoked if a frame that wants modal access is opened */
		public void modalDialogOpened(GUIEvent e){
		 
		    // enable textual DnD in case that the opened model dialog
		    // is the ApplyTacletDialog
		    final boolean enableDnD = e.getSource() instanceof ApplyTacletDialog;
		    listener.setModalDragNDropEnabled(enableDnD);
		    listener.setRefreshHighlightning(enableDnD);
                    
                    // disable drag and drop instantiation of taclets
                    getDropTarget().setActive(false);
		}
		
		/** invoked if a frame that wants modal access is closed */
		public void modalDialogClosed(GUIEvent e){
		    if (e.getSource() instanceof ApplyTacletDialog){
			// disable drag'n'drop ...
			listener.setModalDragNDropEnabled(false);
		    } 

		    listener.setRefreshHighlightning(true);
		    
                    
		    // enable drag and drop instantiation of taclets
                    getDropTarget().setActive(true);
		}
		
		/** invoked if the user wants to abort the proving session */
		public void shutDown(GUIEvent e){
		}	
	    };
		 
	addMouseListener(listener);
	addMouseMotionListener(listener);	
	addKeyListener(listener);


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
        mediator().addGUIListener(guiListener);
        
        // add a listener to this component
        changeListener = new SeqViewChangeListener();
        addComponentListener(changeListener);                      
        addPropertyChangeListener("font", changeListener);
                  
	addHierarchyBoundsListener(changeListener);
    
    }
    
    public void addNotify() {
        super.addNotify();
        Config.DEFAULT.addConfigChangeListener(configChangeListener);
        updateUI();
    }
    
    public void removeNotify(){
        super.removeNotify();
        Config.DEFAULT.removeConfigChangeListener(configChangeListener);
    }


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
    
    /**
     * returns the default tag used for highligthing
     * @return the default tag used for highlighting
     */
    public Object getDefaultHighlight() {
        return defaultHighlight;
    }

    /** 
     * sets the correct highlighter for the given color  
     * @param tag the Object used as tag for highlighting     
     */
    public void setCurrentHighlight(Object tag) {                
        currentHighlight = tag;
    }
    
    /**
     * returns the current tag used for highligthing
     * @return the current tag used for highlighting
     */
    public Object getCurrentHighlight() {        
        return currentHighlight;
    }

    /**
     * removes highlight by setting it to position (0,0)
     */
    public void disableHighlight(Object highlight) {
        try {
            getHighlighter().changeHighlight(highlight,0,0);
        } catch (BadLocationException e) {
            Debug.out("Invalid range for highlight");
        }
    }
    
    /**
     * removes the term and first statement highlighter by setting them to 
     * position (0,0)     
     */
    public void disableHighlights() {
        disableHighlight(currentHighlight);
        disableHighlight(additionalHighlight);        
    }
    
    public void updateUI() {
	super.updateUI();
	setSequentViewFont();       
    }

    private void setSequentViewFont() {
	Font myFont = UIManager.getFont(Config.KEY_FONT_CURRENT_GOAL_VIEW);
        if (myFont != null) {
	    setFont(myFont);
	} else {
	    Debug.out("KEY_FONT_CURRENT_GOAL_VIEW not available. Use standard font.");
	}        
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
        
	restorePosition();
        addMouseMotionListener(listener);
	addMouseListener(listener);        
	repaint();
    }
     
    /** makes the last caret position visible (if possible) */
    private void restorePosition() {
	int lastCaretPos = getLastHighlightedCaretPos();
        if (!(lastCaretPos < 0 || getDocument() == null || 
	      lastCaretPos > getDocument().getLength())) {
	    setCaretPosition(lastCaretPos);
	}
    }

    void setLastHighlightedCaretPos(int pos) {
	lastHighlightedCaretPos = pos;
    }

    int getLastHighlightedCaretPos() {
	return lastHighlightedCaretPos;
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
    public LogicPrinter printer() {
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
    

    /** the startposition and endposition+1 of the string to be
     * highlighted
     * @param p the mouse pointer coordinates
     */
    public void paintHighlights(Point p) {
	// Change highlight for additional Java statement ...
	paintHighlight(getFirstStatementRange(p), additionalHighlight);
	// Change Highlighter for currently selected sequent part 
	paintHighlight(getHighlightRange(p), currentHighlight);
    }

    /** returns the mediator of this view
     * @return the KeYMediator
     */
    public KeYMediator mediator() {
	return mediator;
    }

    /** selected rule to apply 
     * @param taclet the selected Taclet
     * @param pos the PosInSequent describes the position where to apply the 
     * rule 
     */
    void selectedTaclet(TacletApp taclet, PosInSequent pos) {
    	mediator().selectedTaclet(taclet, pos);
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
       String s;
       try{
	   PosInSequent pos = listener.getMousePos();
	   s = getText(pos.getBounds().start(),
		       pos.getBounds().length());
       } catch (Exception ble) { // whatever it is -- forget about it
	   s="";
       }
       return s;
    }
    
	
    public PosInSequent getMousePosInSequent() {
       return listener.getMousePos();
    }


    /** Get a PosInSequent object for a given coordinate of the 
     * displayed sequent. */
    protected synchronized PosInSequent getPosInSequent(Point p) {
	String seqText = getText();
	if (seqText.length() > 0) {
	    int characterIndex = correctedViewToModel(p);
	    
	    return printer().getInitialPositionTable().
		getPosInSequent(characterIndex, filter);
	} else {
	    return null;
	}
    }

    /** Get the character range to be highlighted for the given
     * coordinate in the displayed sequent. */
    synchronized Range getHighlightRange(Point p) {
	String seqText = getText();
	if (seqText.length() > 0) {
	    int characterIndex = correctedViewToModel(p);	    
	    return printer().getInitialPositionTable().
		rangeForIndex(characterIndex);
	} else {
	    return null;
	}
    }

    /** Get the character range to be highlighted for the first
     * statement in a java block at the given
     * coordinate in the displayed sequent.  Returns null
     * if there is no java block there.*/
    protected synchronized Range getFirstStatementRange(Point p) {
	String seqText = getText();
	if (seqText.length() > 0) {
	    int characterIndex = correctedViewToModel(p);
	    
	    return printer().getInitialPositionTable().
		firstStatementRangeForIndex(characterIndex);
	} else {
	    return null;
	}
    }

    /** Return the character index for a certain coordinate.  The
     * usual viewToModel is focussed on inter-character spaces, not
     * characters, so it returns the correct index in the
     * left half of the glyph but one too many in the right half.
     * Therefore, we get width of character before the one given
     * by viewToModel, substract it from the given x value, and get
     * the character at the new position. That is the correct one.  
     */
    public int correctedViewToModel(Point p) {
	String seqText = getText();

	int cursorPosition = viewToModel(p);
	
	cursorPosition -= ( cursorPosition > 0 ? 1 : 0);
	
	cursorPosition = (cursorPosition >= seqText.length() 
			  ? seqText.length()-1 :  
			  cursorPosition);
	cursorPosition = ( cursorPosition >= 0 ? cursorPosition : 0);
	int previousCharacterWidth =
	    getFontMetrics(getFont()).charWidth
	    (seqText.charAt(cursorPosition));	    	    
	
	int characterIndex = viewToModel
	    (new Point( (int)p.getX() - (previousCharacterWidth/2), 
			    (int)p.getY())); 

	return characterIndex;
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






