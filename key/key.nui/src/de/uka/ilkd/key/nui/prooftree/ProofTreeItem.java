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

import de.uka.ilkd.key.nui.prooftree.ProofTreeStyler.StyleConfiguration;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;

/**
 * A node of the javafx tree item that is used in proof trees.
 * 
 * @author Matthias Schultheis
 *
 */
public class ProofTreeItem extends TreeItem<NUINode> {

    /**
     * The internal list for managing children. This is used e. g. to add
     * children.
     */
    private ObservableList<ProofTreeItem> internalChildren;

    /**
     * The list that shows children to display. This is a filtered version of
     * internalChildren.
     */
    private FilteredList<ProofTreeItem> filteredChildren;

    /**
     * Contains the fact if the item is supposed to be visible.
     */
    private boolean visible = false;

    /**
     * Constructor.
     * 
     * @param value
     *            The NUINode encapsulated in the tree item.
     */
    public ProofTreeItem(final NUINode value) {
        super(value);

        internalChildren = FXCollections.observableArrayList();
        filteredChildren = new FilteredList<ProofTreeItem>(internalChildren);

        setAllChildren(filteredChildren);
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
            for (ProofTreeItem child : internalChildren) {
                final boolean childTestResult = child.filter(filter);

                if (childTestResult) {
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
     * Sets the 'children' field of the tree item. This works by reflection.
     * 
     * @param list
     *            The children list to set.
     */
    protected void setAllChildren(final ObservableList<ProofTreeItem> list) {
        try {
            final Field childrenField = TreeItem.class
                    .getDeclaredField("children");
            childrenField.setAccessible(true);
            childrenField.set(this, list);

            final Field declaredField = TreeItem.class
                    .getDeclaredField("childrenListener");
            declaredField.setAccessible(true);

            list.addListener(
                    (ListChangeListener<? super ProofTreeItem>) declaredField
                            .get(this));
        }
        catch (NoSuchFieldException | SecurityException
                | IllegalArgumentException | IllegalAccessException e) {
            throw new RuntimeException("Could not set TreeItem.children", e);
        }
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
     * @return true iff the node is visible
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
     * Applies the visibility information of children that was stored with
     * 'setVisible'.
     */
    public void applyVisibilitiyOfChildren() {

        // define new predicate for the filtered children list
        final Predicate<ProofTreeItem> pred = new Predicate<ProofTreeItem>() {
            @Override
            public boolean test(final ProofTreeItem pti) {
                return pti.isVisible();
            }
        };
        filteredChildren.setPredicate(pred);
    }

}
