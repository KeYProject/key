package de.uka.ilkd.key.nui.prooftree;

import de.uka.ilkd.key.nui.IconFactory;
import javafx.beans.value.ChangeListener;
import javafx.beans.value.ObservableValue;
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
     * The IconFactory used to create the required icons.
     */
    private final IconFactory icf;

    /**
     * The icon that will be displayed left next to the label.
     */
    private ImageView icon;

    private FilteringHandler fh;

    /**
     * The label that will be displayed.
     */
    private Label label;

    private final ChangeListener<Boolean> searchResultListener = new ChangeListener<Boolean>() {
        @Override
        public void changed(ObservableValue<? extends Boolean> observable,
                Boolean didMatchSearch, Boolean nowMatchesSearch) {
            final ObservableList<String> styles = getStyleClass();
            final String cssClassHighlight = ProofTreeStyleConstants.CSS_NODE_HIGHLIGHT;
            if (nowMatchesSearch && !styles.contains(cssClassHighlight)) {
                styles.add(cssClassHighlight);
            }
            if (nowMatchesSearch) {
                styles.remove(cssClassHighlight);
            }
            ProofTreeCell.this.updateItem(ProofTreeCell.this.getItem(), false);
        }
    };

    /**
     * The constructor of the ProofTreeCell.
     * 
     * @param icf
     *            the icon factory used to display node icons
     */
    public ProofTreeCell(final IconFactory icf, final FilteringHandler fh) {
        super();
        this.fh = fh;
        this.icf = icf;
    }

    /**
     * @param icon
     *            the icon to set
     */
    void setIcon(final ImageView icon) {
        this.icon = icon;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected final void updateItem(final NUINode item, final boolean empty) {

        if (getItem() != null) {
            getItem().removeSearchResultListener(searchResultListener);
        }

        super.updateItem(item, empty);

        if (item == null) {
            getStyleClass().remove(ProofTreeStyleConstants.CSS_NODE_HIGHLIGHT);

        }
        else {
            item.addSearchResultListener(searchResultListener);
            if (item.isSearchResult()) {
                if (!getStyleClass()
                        .contains(ProofTreeStyleConstants.CSS_NODE_HIGHLIGHT)) {
                    getStyleClass()
                            .add(ProofTreeStyleConstants.CSS_NODE_HIGHLIGHT);
                }
            }
            else {
                getStyleClass()
                        .remove(ProofTreeStyleConstants.CSS_NODE_HIGHLIGHT);
            }
        }

        // if null node, display nothing
        if (empty || item == null) {
            setText(null);
            setGraphic(null);
            return;
        }

        setContextMenu(new ProofTreeContextMenu(getTreeItem(), getTreeView(),
                icf, fh));

        // reset label and icon
        label = new Label(item.getLabel() + " ");
        icon = null;

        // set decoration (style, icon)
        ProofTreeStyler pts = new ProofTreeStyler(this);
        // applies the style assigned in ProofTreeConverter to the
        // current ProofTreeCell
        pts.applyStyle(getItem());

        // workaround to display an icon next to a label
        setText(null);

        if (icon == null) {
            setGraphic(label);
        }
        else {
            final HBox hbox = new HBox();
            hbox.setSpacing(ICON_SPACING);

            final Label iconLabel = new Label();
            iconLabel.setGraphic(icon);

            hbox.getChildren().addAll(iconLabel, label);
            setGraphic(hbox);
        }
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
}
