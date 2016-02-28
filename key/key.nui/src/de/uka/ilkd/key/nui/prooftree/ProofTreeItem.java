package de.uka.ilkd.key.nui.prooftree;

import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.scene.control.TreeItem;
import javafx.beans.binding.Bindings;
import javafx.beans.binding.ObjectBinding;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;

import java.lang.reflect.Field;
import java.util.concurrent.Callable;
import java.util.function.Predicate;

import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;

/**
 * A node of the javafx tree item that is used in proof trees.
 * @author Matthias Schultheis
 *
 */
public class ProofTreeItem extends TreeItem<NUINode> {
    
    /**
     * The internal list for managing children. This is used
     * e. g. to add children.
     */
    private ObservableList<ProofTreeItem> internalChildren;
    
    /**
     * The list that shows children to display. This is a
     * filtered version of internalChildren.
     */
    private FilteredList<ProofTreeItem> filteredChildren;
    
    /**
     * Contains the fact if the item is supposed to be hidden.
     */
    public boolean hidden = false;

    /**
     * {@inheritDoc}
     */
    public ProofTreeItem(NUINode value) {
        super(value);
        
        internalChildren = FXCollections.observableArrayList();
        filteredChildren = new FilteredList<ProofTreeItem>(internalChildren);
        applyHiddenTag();
        
        setAllChildren(filteredChildren);
    }
    
    /**
     * Applies the hidden status stores in the 'hidden' variable.
     */
    private void applyHiddenTag() {
        
        // define new predicate for the filtered children list
        Predicate<ProofTreeItem> pred = new Predicate<ProofTreeItem>() {
            @Override
            public boolean test(ProofTreeItem t) {
                return t.hidden;
            }
        };
        filteredChildren.setPredicate(pred);
    }
    
    /**
     * Applies a filter to the tree item.
     * @param filter The filter to apply.
     * @return true iff the item is supposed to be displayed after filtering
     */
    public boolean filter(ProofTreeFilter filter) {
        
        // test this item itself
        boolean testResult = filter.test(this.getValue());
        
        if (testResult && !internalChildren.isEmpty()) {
            
            // apply filter to all children and hide node if
            // all children are hidden
            boolean allChildrenHidden = true;
            for (ProofTreeItem child : internalChildren) {
                boolean childTestResult = child.filter(filter);
                
                if(childTestResult) {
                    allChildrenHidden = false;
                }
            }
            
            testResult = !allChildrenHidden;
        }
        
        // store result in hidden field and apply
        hidden = testResult;
        applyHiddenTag();
        
        return hidden;
    }
    
    /**
     * Sets the 'children' field of the tree item.
     * This works by reflection.
     * @param list The children list to set.
     */
    protected void setAllChildren(ObservableList<ProofTreeItem> list) {
        try {
            Field childrenField = TreeItem.class.getDeclaredField("children");
            childrenField.setAccessible(true);
            childrenField.set(this, list);

            Field declaredField = TreeItem.class
                    .getDeclaredField("childrenListener");
            declaredField.setAccessible(true);
            
            list.addListener(
                    (ListChangeListener<? super ProofTreeItem>) declaredField.get(this));
        }
        catch (NoSuchFieldException | SecurityException
                | IllegalArgumentException | IllegalAccessException e) {
            throw new RuntimeException("Could not set TreeItem.children", e);
        }
    }
    
    /**
     * Adds a child to the treeItem.
     * @param child the child to add
     */
    public void addChild(ProofTreeItem child) {
        internalChildren.add(child);
    }
}
