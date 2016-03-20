package de.uka.ilkd.key.nui.prooftree;

import java.lang.reflect.Field;
import java.util.function.Predicate;

import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.collections.transformation.FilteredList;
import javafx.scene.control.TreeItem;

/**
 * A node of the javafx tree item that is used in proof trees.
 * 
 * @author Matthias Schultheis
 *
 */
public class ProofTreeItem extends TreeItem<NUINode> {

    /**
     * The list that shows children to display. This is a filtered version of
     * internalChildren.
     */
    private final FilteredList<ProofTreeItem> filteredChildren;

    /**
     * The internal list for managing children. This is used e. g. to add
     * children.
     */
    private final ObservableList<ProofTreeItem> internalChildren;

    /**
     * Contains the fact if the item is supposed to be visible.
     */
    private boolean visible;

    /**
     * Constructor.
     * 
     * @param value
     *            The NUINode encapsulated in the tree item.
     * @throws NoSuchFieldException
     */
    public ProofTreeItem(final NUINode value) {
        super(value);

        internalChildren = FXCollections.observableArrayList();
        filteredChildren = new FilteredList<>(internalChildren);

        setAllChildren(filteredChildren);
    }

    /**
     * Adds a child to the treeItem.
     * 
     * @param child
     *            the child to add
     */
    public void addChild(final ProofTreeItem child) {
        internalChildren.add(child);
    }

    /**
     * Applies the visibility information of children that was stored with
     * 'setVisible'.
     */
    public void applyVisibilitiyOfChildren() {
        // define new predicate for the filtered children list

        // HINT: DO NOT TRY TO USE JAVA 8 FOR THIS! (or do it and find out why it does not work)

                final Predicate<? super ProofTreeItem> pred = new Predicate<ProofTreeItem>() {
                    @Override
                    public boolean test(final ProofTreeItem pti) {
                        return pti.isVisible();
                    }
                };
                filteredChildren.setPredicate(pred);
    }

    /**
     * Applies a filter to the tree item.
     * 
     * @param filter
     *            The filter to apply.
     * @return true iff the item is supposed to be displayed after filtering
     */
    public boolean filter(final ProofTreeFilter filter) {

        // test this item itself
        boolean testResult = filter.test(this.getValue());

        if (testResult && !internalChildren.isEmpty()) {
            // apply filter to all children and hide node if
            // all children are hidden
            boolean allChildrenHidden = true;

            // check recursively if any child in this subtree is supposed to be
            // displayed after filtering
            for (ProofTreeItem child : internalChildren) {
                if (child.filter(filter)) {
                    allChildrenHidden = false;
                }
            }
            testResult = !allChildrenHidden;
        }

        // store result in hidden field and apply
        setVisible(testResult);
        applyVisibilitiyOfChildren();

        return testResult;
    }
    
    /**
     * TODO
     * @return
     */
    public FilteredList<ProofTreeItem> getFilteredChildren() {
        return filteredChildren;
    }

    /**
     * TODO
     * @return
     */
    public ObservableList<ProofTreeItem> getInternalChildren() {
        return internalChildren;
    }

    /**
     * @return true if this node is visible
     */
    public boolean isVisible() {
        return visible;
    }

    /**
     * Sets the visibility of the node. To apply visibility changese the method
     * 'applyVisibiltiyToChildren' of the parent has to be called afterwards.
     * 
     * @param visible
     *            the visibility of the node.
     */
    public void setVisible(final boolean visible) {
        this.visible = visible;
    }

    /**
     * Sets the 'children' field of the tree item. This works by reflection.
     * 
     * @param list
     *            The children list to set.
     */
    @SuppressWarnings("unchecked")
    protected final void setAllChildren(final ObservableList<ProofTreeItem> list) {
        try {
            final Field childrenField = TreeItem.class.getDeclaredField("children");
            childrenField.setAccessible(true);
            childrenField.set(this, list);

            final Field declaredField = TreeItem.class.getDeclaredField("childrenListener");
            declaredField.setAccessible(true);

            list.addListener((ListChangeListener<? super ProofTreeItem>) declaredField.get(this));
        }
        catch (NoSuchFieldException | SecurityException | IllegalArgumentException
                | IllegalAccessException e) {
            throw new RuntimeException("Could not set TreeItem.children", e);
        }
    }

}
