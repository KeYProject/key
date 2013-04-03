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

import java.awt.Point;
import java.awt.dnd.DragGestureEvent;
import java.awt.dnd.DragGestureListener;
import java.awt.dnd.DragSource;
import java.awt.dnd.DragSourceAdapter;
import java.awt.dnd.DragSourceDropEvent;
import java.awt.dnd.InvalidDnDOperationException;
import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.awt.event.MouseEvent;

import javax.swing.JLabel;
import javax.swing.JPopupMenu;
import javax.swing.SwingUtilities;
import javax.swing.event.PopupMenuEvent;
import javax.swing.event.PopupMenuListener;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.gui.macros.ProofMacroMenu;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.pp.PosInSequent;
import de.uka.ilkd.key.rule.BuiltInRule;
import java.awt.event.MouseListener;
import java.awt.event.MouseMotionListener;



/** reacts on mouse events to highlight the selected part of the
 * sequent and it pops up a menu showing all applicable Taclet 
 * at the highlighted position if the mouse is pressed
 *
 * Additionally it performs all necessary actions for draging some
 * highlighted sequent part into some other GUI component (e.g.
 * some Taclet rule instantiation dialog)
 */
class SequentViewListener
        implements KeyListener, MouseListener, MouseMotionListener {
	
    private KeYMediator mediator;
    private LeafNodeView seqView;

    private TacletMenu menu;
   
    public boolean refreshHighlightning;
    private boolean modalDragNDropEnabled;
    private boolean showTermInfo;

    /** last registered mouse position */
    PosInSequent mousePos = PosInSequent.createSequentPos();

    /** hack to block a click event */
    private long block = 0;

    private DragGestureListener seqViewDragGestureListener;

    SequentViewListener(LeafNodeView seqView,
			KeYMediator mediator) {
	this.mediator = mediator;
	this.seqView = seqView;
	menu = new TacletMenu();
	seqViewDragGestureListener = new SequentViewGestures();
        
        refreshHighlightning = true;
	setModalDragNDropEnabled(false);
    }

    private void highlight(Point p) {
        mousePos = seqView.getPosInSequent(p);            
        seqView.setCurrentHighlight(seqView.defaultHighlight);
        seqView.paintHighlights(p);
        seqView.setLastHighlightedCaretPos(seqView.correctedViewToModel(p));
    }
	
    public void mouseMoved(MouseEvent me) {
        if (me.getSource() == seqView && refreshHighlightning) {
            highlight(me.getPoint());
            if (showTermInfo) {
                final String info = getTermInfo();

                if (info == null) {
                    MainWindow.getInstance().setStandardStatusLine();
                } else {
                    MainWindow.getInstance().setStatusLine(info);
                }
            }
        }
    }
    
    public void mouseExited(MouseEvent me) {
        if (me.getSource() == seqView && refreshHighlightning) {
            seqView.disableHighlights();
        }
    }

    private String getTermInfo() {
        if ((mousePos == null)||
            ("".equals(seqView.getHighlightedText()))) return null;
        Term t  ;
        final PosInOccurrence posInOcc = mousePos.getPosInOccurrence();
        if (posInOcc != null) {
            t = posInOcc.subTerm();
            String tOpClassString = t.op().getClass().toString();
            String operator = tOpClassString.substring(
                tOpClassString.lastIndexOf('.')+1);
            return  operator + ", Sort: " + t.sort() + ", Hash:"+t.hashCode();
        }
        return null;
    }
                	           
    public void mouseClicked(MouseEvent me) {           
        if (!modalDragNDropEnabled()) { 
	    // if a popup menu is cancelled by a click we do not want to 
	    // activate another using the same click event 
	    if (Math.abs(System.currentTimeMillis()-block)>=400) {   
		mousePos = seqView.getPosInSequent(me.getPoint());  
		boolean macroActive = ProofIndependentSettings.DEFAULT_INSTANCE.getGeneralSettings().isRightClickMacro();
//		boolean macroActive = ProofSettings.DEFAULT_SETTINGS.getGeneralSettings().isRightClickMacro();
		if (mediator!= null && mousePos != null) {
		    if (me.isShiftDown()) {
			if (mediator.getInteractiveProver() != null) {
			    mediator.getInteractiveProver().
				startFocussedAutoMode ( mousePos.getPosInOccurrence (),
							mediator.getSelectedGoal () );
			}
		    } else if(macroActive && SwingUtilities.isRightMouseButton(me)) { 
		        ProofMacroMenu macroMenu = new ProofMacroMenu(mediator, 
		                mousePos.getPosInOccurrence());
		        if(macroMenu.isEmpty()) {
		            macroMenu.add(new JLabel("no strategies available"));
		        } 
		        JPopupMenu popupMenu = macroMenu.getPopupMenu();
		        popupMenu.setLabel("Strategy macros");
		        popupMenu.show(seqView, me.getX()-5, me.getY()-5);
		    } else {		    		  
			//done before collecting the taclets because initialising 
			//built in rules may have side effects on the set of applicable
			//taclets
			final ImmutableList<BuiltInRule> builtInRules 
				= mediator.getBuiltInRule(mousePos.getPosInOccurrence());
			
			menu = new TacletMenu(seqView,
					      mediator.getFindTaclet(mousePos), 
					      mediator.getRewriteTaclet(mousePos),
					      mediator.getNoFindTaclet(),
					      builtInRules,
					      mousePos);                               

			refreshHighlightning = false;  

			final JPopupMenu popup = menu.getPopupMenu();

			popup.addPopupMenuListener(new PopupMenuListener() {
				public void popupMenuCanceled(PopupMenuEvent e) {                            
				    block = System.currentTimeMillis();
				}

				public void popupMenuWillBecomeInvisible(PopupMenuEvent e) {
				    refreshHighlightning = true;
				    block = System.currentTimeMillis();
				}
			    
				public void popupMenuWillBecomeVisible(PopupMenuEvent e) {
				    refreshHighlightning = false;			    
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
    
    public void mouseDragged(MouseEvent me) {
        // Needs to be implemented for MouseMotionListener
    }
    
    public void mousePressed(MouseEvent me){
        // Needs to be implemented for MouseListener
    }

    public void mouseReleased(MouseEvent me) {                
        if  (!modalDragNDropEnabled() && menu.isPopupMenuVisible() &&      
                !menu.getPopupMenu().contains(me.getX()-menu.getX(), 
                                              me.getY()-menu.getY())) {
            hideMenu();
	}
    }
    
    public void mouseEntered(MouseEvent me) {
        seqView.requestFocusInWindow(); // <-- What for?
    }
    
    public void hideMenu(){
        menu.setPopupMenuVisible(false);
    }

    public synchronized void setModalDragNDropEnabled(boolean allowDragNDrop) {
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
            
            if (info == null) {
                MainWindow.getInstance().setStandardStatusLine();
            } else {                    
            	MainWindow.getInstance().setStatusLine(info);
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
            MainWindow.getInstance().setStandardStatusLine();
        }
    }

    /* (non-Javadoc)
     * @see java.awt.event.KeyListener#keyTyped(java.awt.event.KeyEvent)
     */
    public void keyTyped(KeyEvent e) {                        
        
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
	    final Object dndHighlight =
                    seqView.getColorHighlight(LeafNodeView.DND_HIGHLIGHT_COLOR);
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
                                      @Override
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
