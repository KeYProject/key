// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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
import java.util.Iterator;
import java.util.Vector;

import javax.swing.*;
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
 * The sequent view displays the sequent of an open goal and allows selection of
 * formulas as well as the application of rules. It offers services for highlighting 
 * formulas, selecting applicable rules (in particular taclets) and drag'n drop
 * instantiation of taclets.
 */
public class SequentView extends JEditorPane implements Autoscroll {
            
    public static final Color DEFAULT_HIGHLIGHT_COLOR = Color.yellow;

    public static final Color UPDATE_HIGHLIGHT_COLOR = new Color(255, 230, 230);

    // the default tag of the highlight
    private Object defaultHighlight;

    // the current tag of the highlight
    private Object currentHighlight;

    // an additional highlight to mark the first active statement
    private Object additionalHighlight;

    // a vector of highlights to mark updates
    private Vector<Object> updateHighlights;

    // all known highlights
    private HashMap<Color, DefaultHighlightPainter> color2Highlight = 
        new HashMap<Color, DefaultHighlightPainter>();
    
    // the used sequentprinter
    private LogicPrinter printer;

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
    public SequentView(KeYMediator mediator) {
	/* setting this to text/html causes the position tables to go wrong */
	super("text/plain","");
	setMediator(mediator);
	// view cannot be edited
	setEditable(false);
	// disables selection
	setSelectionColor(getBackground());
	// sets the painter for the highlightning
	setHighlighter(new DefaultHighlighter());	
	//sets initial highlight (not visible) and stores its tag

        // REMARK: THE ORDER FOR ADDING HIGHLIGHTS IS CRUCIAL
	// WHEN USING OVERLAPPING HIGHLIGHTS:
	// Adding highlight H1 before highlight H2 ensures that 
	// H1 can overwrite overlapping parts of H2 !!!
        	        
	additionalHighlight = getColorHighlight(Color.lightGray); 		
	defaultHighlight = getColorHighlight(DEFAULT_HIGHLIGHT_COLOR);
	
	currentHighlight = defaultHighlight;
	updateHighlights = new Vector<Object>();
		
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
            Main.getInstance().notify(new GeneralFailureEvent(e.getMessage()));
        }finally{
            try {
                super.finalize();
            } catch (Throwable e) {
                Main.getInstance().notify(new GeneralFailureEvent(e.getMessage()));
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
     * updates all updateHighlights. Firstly removes all displayed ones and
     * then gets a new list of updates to highlight
     */
    public void updateUpdateHighlights() {
        if (printer == null) return;

        Iterator<Object> it = updateHighlights.iterator();

        while (it.hasNext()) {
            removeHighlight(it.next());
        }

        updateHighlights.clear();
        Range[] ranges = printer.getPositionTable().getUpdateRanges();

        if (ranges != null) {
            for (int i = 0; i < ranges.length; i++) {
                Object tag = getColorHighlight(UPDATE_HIGHLIGHT_COLOR);
                updateHighlights.addElement(tag);
                paintHighlight(ranges[i], tag);
            }
        }
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
    
    
    /**
     * returns the highlight painter for the specified color 
     * @param color the Color the HighlightPainter shall use    
     * @return the highlight painter for the specified color
     */
    private HighlightPainter getColorHighlightPainter(Color color) {
        if (!color2Highlight.containsKey(color)) {
           color2Highlight.put(color, new DefaultHighlighter.
                   DefaultHighlightPainter(color));
        } 
        return color2Highlight.get(color);
    }
    
    /**
     * registers a highlighter that marks the regions specified by the returned 
     * tag with the given color
     * @param color the Color used to highlight regions of the sequent 
     * @return the highlight for the specified color
     */
    public Object getColorHighlight(Color color) {                                    
        Object highlight = null;
        try {
            highlight =
                getHighlighter().addHighlight(0,0,
                        getColorHighlightPainter(color));                        
        } catch (BadLocationException e) {
            Debug.out("Highlight range out of scope.");
        }      
        return highlight;
    }
    
    /**
     * d a highlighter that marks the regions specified by the returned 
     * tag with the given color
     * @param highlight the Object used as tag for the highlight 
     */
    public void removeHighlight(Object highlight) {                                    
        getHighlighter().removeHighlight(highlight);                                
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
	updateUpdateHighlights();

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

    // xxx remove?
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
        

    /** 
     * highlights the elements in the given range using the specified
     * highlighter 
     * @param range the Range to be highlighted
     * @param highlighter the Object painting the highlight
     */
    void paintHighlight(Range range, Object highlighter) {
	try {	
	    // Change highlight for additional Java statement ...
	    if (range != null) {
		getHighlighter()
		    .changeHighlight(highlighter, 
				     range.start(), range.end());
	    } else {
		getHighlighter()
		    .changeHighlight(highlighter, 0, 0);
	    }
	} catch(BadLocationException badLocation) {
	   System.err.println("SequentView tried to highlight an area" + 
			      "that is not existing.");
	    System.err.println("Exception:"+badLocation);
	}	
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
	    
	    return printer().getPositionTable().
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
	    return printer().getPositionTable().
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
	    
	    return printer().getPositionTable().
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

    
}






