package de.uka.ilkd.key.nui.prooftree;

import de.uka.ilkd.key.nui.IconFactory;
import de.uka.ilkd.key.nui.controller.TreeViewController;
import javafx.beans.value.ChangeListener;
import javafx.collections.ObservableList;
import javafx.scene.control.Label;
import javafx.scene.control.TreeCell;
import javafx.scene.image.ImageView;
import javafx.scene.layout.HBox;

/**
 * This class is responsible for rendering of a tree cell.
 * 
 * @author Matthias Schultheis
 * @version 1.0
 */
public class ProofTreeCell extends TreeCell<NUINode> {

    /**
     * The icon size in px.
     */
    public static final int ICON_SIZE = 15;

    /**
     * Space between icon and label in px.
     */
    public static final int ICON_SPACING = 5;

    /**
     * The filtering handler used to filter the tree's cells.
     */
    private FilteringHandler filteringHandler;

    /**
     * The IconFactory used to create the required icons.
     */
    private final IconFactory iconFactory;

    /**
     * The icon that will be displayed left next to the label.
     */
    private ImageView icon;

    /**
     * The label that will be displayed.
     */
    private Label label;

    /**
     * The change listener registered to this ProofTreeCell.
     */
    private final ChangeListener<Boolean> searchResultListener = (observable,
            didMatchSearch, nowMatchesSearch) -> {
        final ObservableList<String> styles = getStyleClass();
        final String cssClassHighlight = ProofTreeStyleConstants.CSS_NODE_HIGHLIGHT;
        if (nowMatchesSearch && !styles.contains(cssClassHighlight)) {
            styles.add(cssClassHighlight);
        }
        if (nowMatchesSearch) {
            styles.remove(cssClassHighlight);
        }
        ProofTreeCell.this.updateItem(ProofTreeCell.this.getItem(), false);
    };

    /**
     * The treeViewController used to handle the actions of the treeView.
     */
    private final TreeViewController treeViewController;

    /**
     * Returns the TreeViewController associated with the ProofTreeCell.
     * 
     * @return the {@link TreeViewController}.
     */
    public TreeViewController getTreeViewController() {
        return treeViewController;
    }

    /**
     * The constructor of the ProofTreeCell.
     * 
     * @param icf
     *            the {@link IconFactory} used to display node icons
     * @param fh
     *          the {@link FilteringHandler} used to filter this ProofTreeCell
     * @param tvc
     *          the {@link TreeViewController} associated with the TreeView
     */

    public ProofTreeCell(final IconFactory icf, final FilteringHandler filteringHandler,
            final TreeViewController treeViewController) {

        super();
        this.filteringHandler = filteringHandler;
        this.iconFactory = icf;
        this.treeViewController = treeViewController;
    }

    /**
     * Returns the icon factory associated with the ProofTreeCell.
     * 
     * @return the {@link IconFactory}.
     */
    public IconFactory getIconFactory() {
        return iconFactory;
    }

    /**
     * Returns the icon associated with the ProofTreeCell.
     * 
     * @return {@link ImageView} containing the icon for the cell.
     */
    public ImageView getIcon() {
        return this.icon;
    }

    /**
     * Returns the label associated with the ProofTreeCell.
     * 
     * @return label the {@link Label} used by the {@link ProofTreeCell}.
     */
    public Label getLabel() {
        return label;
    }

    /**
     * @param icon
     *            the icon to set
     */
    protected void setIcon(final ImageView icon) {
        this.icon = icon;
    }

    @Override
    protected final void updateItem(final NUINode item, final boolean empty) {

        final String cssHighlighting = ProofTreeStyleConstants.CSS_NODE_HIGHLIGHT;

        if (getItem() != null) {
            getItem().removeSearchResultListener(searchResultListener);
        }

        super.updateItem(item, empty);

        if (item == null) {
            getStyleClass().remove(cssHighlighting);

        }
        else {
            item.addSearchResultListener(searchResultListener);
            if (item.isSearchResult()) {
                if (!getStyleClass().contains(cssHighlighting)) {
                    getStyleClass().add(cssHighlighting);
                }
            }
            else {
                getStyleClass().remove(cssHighlighting);
            }
        }

        // if null node, display nothing
        if (empty || item == null) {
            setText(null);
            setGraphic(null);
            return;
        }

        setContextMenu(new ProofTreeContextMenu(getTreeItem(), getTreeView(),
                iconFactory, filteringHandler, treeViewController));

        // reset label and icon
        label = new Label(item.getLabel() + " ");
        icon = null;

        // set decoration (style, icon)
        final ProofTreeStyler pts = new ProofTreeStyler(this);
        // applies the style assigned in ProofTreeConverter to the
        // current ProofTreeCell
        pts.applyStyle(getItem());

        // workaround to display an icon next to a label
        setText(null);

        if (icon == null) {
            setGraphic(label);
        }
        else {
            final HBox hbox = new HBox(ICON_SPACING);
            final Label iconLabel = new Label("", icon);
            hbox.getChildren().addAll(iconLabel, label);
            setGraphic(hbox);
        }
    }
}
