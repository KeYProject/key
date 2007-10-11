// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.Color;
import java.awt.Point;
import java.awt.dnd.*;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;

import javax.swing.JPopupMenu;
import javax.swing.event.MouseInputAdapter;
import javax.swing.event.PopupMenuEvent;
import javax.swing.event.PopupMenuListener;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.*;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.PosInSequent;



/** reacts on mouse events to highlight the selected part of the
 * sequent and it pops up a menu showing all applicable Taclet 
 * at the highlighted position if the mouse is pressed
 *
 * Additionally it performs all necessary actions for draging some
 * highlighted sequent part into some other GUI component (e.g.
 * some Taclet rule instantiation dialog)
 */
class SequentViewListener extends MouseInputAdapter 
    implements KeyListener  {  
	
    
    static Logger logger = Logger.getLogger(SequentViewListener.class.getName());

    private KeYMediator mediator;
    private SequentView seqView;

    private TacletMenu menu;
   
    
    private boolean refreshHighlightning;
    private boolean modalDragNDropEnabled;
    private boolean showTermInfo;

    
    private Object mouseOverHighlight;

    /** last registered mouse position */
    PosInSequent mousePos = PosInSequent.createSequentPos();


    /** hack to block a click event */
    private long block = 0;
    

    private DragGestureListener seqViewDragGestureListener;

    SequentViewListener(SequentView seqView,
			KeYMediator mediator) {
	this.mediator = mediator;
	this.seqView = seqView;

        mouseOverHighlight = seqView.getDefaultHighlight();
	menu = new TacletMenu();     

	seqViewDragGestureListener = new SequentViewGestures();
	
        
	setRefreshHighlightning(true);
	setModalDragNDropEnabled(false);
    }

    
    private void highlight(Point p) {
        mousePos = seqView.getPosInSequent(p);            
        seqView.setCurrentHighlight(mouseOverHighlight);
        seqView.paintHighlights(p);
        seqView.setLastHighlightedCaretPos(seqView.correctedViewToModel(p));
    }
	
    public void mouseMoved(MouseEvent me) {	    
	if (me.getSource() == seqView && refreshHighlightning())  { 
	    highlight(me.getPoint());            
            if (showTermInfo) { 
                final String info = getTermInfo();
               
                final Main main = ((Main)mediator.mainFrame());
                if (info == null) {
                    main.setStandardStatusLine();
                } else {                    
                    main.setStatusLine(info);
                }
            }	    
	}
    }       
    
    private String getTermInfo() {
        if ((mousePos == null)||
            ("".equals(seqView.getHighlightedText()))) return null;
        Term t = null;
        final PosInOccurrence posInOcc = mousePos.getPosInOccurrence();
        if (posInOcc != null) {
            t = posInOcc.subTerm();
            String tOpClassString = t.op().getClass().toString();
            String operator = tOpClassString.substring(
                tOpClassString.lastIndexOf('.')+1);
            return  operator + ", Sort: " + t.sort();
        }
        return null;
    }
                	           
    public void mouseClicked(MouseEvent me) {                
        if (!modalDragNDropEnabled()) { 
	    // if a popup menu is cancelled by a click we do not want to 
	    // activate another using the same click event 
	    if (Math.abs(System.currentTimeMillis()-block)>=400) {   
		mousePos = seqView.getPosInSequent(me.getPoint());                                    
		if (mediator!= null && mousePos != null) {
		    if (me.isShiftDown()) {
			if (mediator.getInteractiveProver() != null) {
			    mediator.getInteractiveProver().
				startFocussedAutoMode ( mousePos.getPosInOccurrence (),
							mediator.getSelectedGoal () );
			}
		    } else {		    		    
		    
			menu = new TacletMenu(seqView,
					      mediator.getFindTaclet(mousePos), 
					      mediator.getRewriteTaclet(mousePos),
					      mediator.getNoFindTaclet(),
					      mediator.getBuiltInRule(mousePos.getPosInOccurrence()),
					      mousePos);                               

			setRefreshHighlightning(false);                    

			final JPopupMenu popup = menu.getPopupMenu();

			popup.addPopupMenuListener(new PopupMenuListener() {
				public void popupMenuCanceled(PopupMenuEvent e) {                            
				    block = System.currentTimeMillis();
				}

				public void popupMenuWillBecomeInvisible(PopupMenuEvent e) {
				    setRefreshHighlightning(true);
				    block = System.currentTimeMillis();
				}
			    
				public void popupMenuWillBecomeVisible(PopupMenuEvent e) {
				    setRefreshHighlightning(false);			    
				}
			    });
                    
			popup.show(seqView, me.getX() - 5, me.getY() - 5);            
			popup.requestFocusInWindow();                    
		    }
		} else {
		    hideMenu();
		    highlight(me.getPoint());
		}
	    } else {
		highlight(me.getPoint());
	    }
	}
    }

    public void mouseReleased(MouseEvent me) {                
        if  (!modalDragNDropEnabled() && menu.isPopupMenuVisible() &&      
                !menu.getPopupMenu().contains(me.getX()-menu.getX(), 
                                              me.getY()-menu.getY())) {
            hideMenu();
	}
    }
    
    public void mouseEntered(MouseEvent me) {
        seqView.requestFocusInWindow();
    }
    
    public void hideMenu(){
        menu.setPopupMenuVisible(false);        
    }


    public synchronized void setRefreshHighlightning(boolean doRefresh){
	refreshHighlightning = doRefresh;
    }
	
    public synchronized boolean refreshHighlightning(){
	return refreshHighlightning;
    }

	
    public synchronized void setModalDragNDropEnabled(boolean allowDragNDrop){
	modalDragNDropEnabled = allowDragNDrop;
    }
	
    public synchronized boolean modalDragNDropEnabled(){
	return modalDragNDropEnabled;
    }
	
    protected PosInSequent getMousePos() {
	return mousePos;
    }	
    
    /* (non-Javadoc)
     * @see java.awt.event.KeyListener#keyPressed(java.awt.event.KeyEvent)
     */
    public void keyPressed(KeyEvent e) {
      if ((e.getModifiersEx() & InputEvent.ALT_DOWN_MASK) != 0) {
            synchronized(this) {
                showTermInfo = true;	    
            }
            final String info = getTermInfo();
            
            final Main main = ((Main)mediator.mainFrame());
            if (info == null) {
                main.setStandardStatusLine();
            } else {                    
                main.setStatusLine(info);
            }
        }
    }


    /* (non-Javadoc)
     * @see java.awt.event.KeyListener#keyReleased(java.awt.event.KeyEvent)
     */
    public void keyReleased(KeyEvent e) {
        if ((e.getModifiersEx() & InputEvent.ALT_DOWN_MASK)==0 && showTermInfo) { 
            synchronized(this) {
                showTermInfo = false;
            }
            ((Main)mediator.mainFrame()).setStandardStatusLine();
        }
    }

    /* (non-Javadoc)
     * @see java.awt.event.KeyListener#keyTyped(java.awt.event.KeyEvent)
     */
    public void keyTyped(KeyEvent e) { 
        final char ch = e.getKeyChar();                             
        if (ch == '/') {    
            synchronized(IncrementalSearch.class) {
                new IncrementalSearch(seqView);
            }
        }                        
    }
   
    public DragGestureListener getDragGestureListener() {
	return seqViewDragGestureListener;
    }


    private class SequentViewGestures implements DragGestureListener {
	/**
	 * a drag gesture has been initiated
	 */	
	public void dragGestureRecognized(DragGestureEvent dgEvent) {	
	    final Object oldHighlight = seqView.getCurrentHighlight();	
	    final Object dndHighlight = seqView.getColorHighlight(Color.green);            
	    seqView.updateUpdateHighlights();
	
	    seqView.setCurrentHighlight(dndHighlight);
	
	    hideMenu();
	
	    Point dragOrigin = dgEvent.getDragOrigin();
	    PosInSequent localMousePos = seqView.getPosInSequent(dragOrigin);
	
	    if (localMousePos != null) {
		try {
		    seqView.getDragSource().
			startDrag(dgEvent, 
				  DragSource.DefaultCopyDrop, 
				  new PosInSequentTransferable(localMousePos,
				      mediator.getServices()),
				  new DragSourceAdapter() {
				      public void dragDropEnd(DragSourceDropEvent event) {
					  // Enable updating the subterm 
					  // highlightning ...
					  seqView.removeHighlight(dndHighlight);
					  seqView.setCurrentHighlight(oldHighlight);
				      }});
		} catch(InvalidDnDOperationException dnd) {
		    // system not in proper dnd state
		    // Enable updating the subterm 
		    // highlightning ...
		    seqView.removeHighlight(dndHighlight);
		    seqView.setCurrentHighlight(oldHighlight);		
		}
	    }        	    	  
	}
    }

}
