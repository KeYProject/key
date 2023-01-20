package sourcerer;

import javax.swing.event.ChangeEvent;
import javax.swing.event.ChangeListener;
import javax.swing.event.EventListenerList;

import recoder.ModelElement;
import recoder.java.ProgramElement;

public class DefaultSelectionModel implements SelectionModel {

    private ModelElement root;
    private ModelElement element;


    public DefaultSelectionModel() { }

    public ModelElement getRoot() {
	if (root == null && (element instanceof ProgramElement)) {
	    root = element;
	    ProgramElement parent = (root == null) 
		? null 
		: ((ProgramElement)root).getASTParent();
	    while (parent != null) {
		root = parent;
		parent = parent.getASTParent();
	    }
	}
	return root;
    }

    public ModelElement getSelectedElement() {
	return element;
    }

    public void setSelectedElement(ModelElement element) {
	if (this.element != element) {
	    this.element = element;
	    this.root = null;
	    fireStateChanged();
	}
    }

    protected transient ChangeEvent changeEvent;

    protected EventListenerList listenerList;
   
    /**
     * Adds a ChangeListener. 
     *
     * @param l the ChangeListener to add
     * @see #removeChangeListener
     */
    public void addChangeListener(ChangeListener l) {
	if (listenerList == null) {
	    listenerList = new EventListenerList();
	}
        listenerList.add(ChangeListener.class, l);
    }

    /**
     * Removes a ChangeListener.
     *
     * @param l the ChangeListener to remove
     * @see #addChangeListener
     */
    public void removeChangeListener(ChangeListener l) {
	if (listenerList == null) {
	    listenerList = new EventListenerList();
	}
        listenerList.remove(ChangeListener.class, l);
    }

    /** 
     * Calls each ChangeListener's stateChanged() method.
     */
    protected void fireStateChanged() {
	if (listenerList == null) {
	    return;
	}
        Object[] listeners = listenerList.getListenerList();
        for (int i = listeners.length - 2; i >= 0; i -=2 ) {
            if (listeners[i] == ChangeListener.class) {
                if (changeEvent == null) {
                    changeEvent = new ChangeEvent(this);
                }
                ((ChangeListener)listeners[i+1]).stateChanged(changeEvent);
            }          
        }
    }   
}

