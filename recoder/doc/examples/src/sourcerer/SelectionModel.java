package sourcerer;

import javax.swing.event.ChangeListener;

import recoder.ModelElement;

public interface SelectionModel {
    /**
       Convenience method to find the topmost parent of the specified element,
       if any.
     */
    ModelElement getRoot();
    ModelElement getSelectedElement();
    void setSelectedElement(ModelElement element);
    void addChangeListener(ChangeListener e);
    void removeChangeListener(ChangeListener e);
}


