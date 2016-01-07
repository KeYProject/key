package de.uka.ilkd.key.nui.prooftree;

import de.uka.ilkd.key.nui.IconFactory;
import javafx.scene.control.Label;
import javafx.scene.control.TreeCell;
import javafx.scene.image.ImageView;
import javafx.scene.layout.HBox;

/**
 * This class is responsible for rendering of a tree cell.
 * @author  Matthias Schultheis
 * @version 1.0
 */
public class ProofTreeCell extends TreeCell<NUINode> {
	
    /**
     * The icon size in px.
     */
    private final int iconSize = 15;
    
    /**
     * Space between icon and label in px.
     */
    private final int iconSpacing = 5;
        
    /**
     * The label that will be displayed.
     */
	private Label label;

    /**
     * The IconFactory used to create the required icons.
     */
    private IconFactory icf;
    
    /**
     * The icon that will be displayed left next to the label.
     */
	private ImageView icon;
	
	/**
	 * The constructor of the ProofTreeCell.
	 */
	public ProofTreeCell() {
		super();
		icf = new IconFactory(iconSize, iconSize);
	}
	
	/**
	 * @param icon the icon to set
	 */
	private void setIcon(final ImageView icon) {
		this.icon = icon;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected final void updateItem(final NUINode item, final boolean empty) {
		// remove styles from last items
		getStyleClass().remove(ProofTreeStyle.CSS_NODE_HIGHLIGHTED);
		
		super.updateItem(item, empty);
		
		// if null node, display nothing
		if (empty || item == null) {
			setText(null);
			setGraphic(null);
			return;
		}
		
		setContextMenu(new ProofTreeContextMenu(item, getTreeItem()));
		
		// reset label and icon
	    label = new Label(item.getLabel() + " ");
	    icon  = null;
	    
        // set decoration (style, icon)
		if (item instanceof NUIInnerNode) {
			decorateAsInnerNode();
		} else if (item instanceof NUIBranchNode) {
			decorateAsBranchNode();
		} else if (item instanceof NUILeafNode) {
			decorateAsLeafNode();
		}
		
		if (item.isHighlighted()) {
			this.getStyleClass().add(ProofTreeStyle.CSS_NODE_HIGHLIGHTED);
		}
        
		// workaround to display an icon next to a label
		setText(null);
		if (icon != null) {
		    HBox hbox = new HBox();
		    hbox.setSpacing(iconSpacing);
		    
		    Label iconLabel = new Label();
		    iconLabel.setGraphic(icon);
		    
		    hbox.getChildren().addAll(iconLabel, label);
	        setGraphic(hbox);
		} else {
			setGraphic(label);
		}
	}
	
	
	/**
	 * Decorates the cell as InnerNode by modifying label and icon
	 * Assigns CSS style classes and icon images.
	 */
	private void decorateAsInnerNode() {
		if (getItem().isInteractive()) {
			setIcon(icf.getImage(IconFactory.KEY_INNER_NODE_INTERACTIVE));
		}
	}

	/**
	 * Decorates the cell as BranchNode by modifying label and icon
	 * Assigns CSS style classes and icon images.
	 */
	private void decorateAsBranchNode() {
		label.getStyleClass().add(ProofTreeStyle.CSS_NODE_BRANCH);
		if (getItem().isClosed()) {
			label.getStyleClass().add(ProofTreeStyle.CSS_NODE_CLOSED);
			setIcon(icf.getImage(IconFactory.KEY_BRANCH_NODE_CLOSED));
		} else {
			if (getItem().isLinked()) {
				setIcon(icf.getImage(IconFactory.KEY_BRANCH_NODE_LINKED));
			} else {
				setIcon(icf.getImage(IconFactory.KEY_BRANCH_NODE_OPEN));
			}	
		}
	}

	/**
	 * Decorates the cell as LeafNode by modifying label and icon
	 * Assigns CSS style classes and icon images.
	 */
	private void decorateAsLeafNode() {
		label.getStyleClass().add(ProofTreeStyle.CSS_NODE_LEAF);
		// leaf node is a closed goal
		if (getItem().isClosed()) {
			setIcon(icf.getImage(IconFactory.KEY_LEAF_NODE_CLOSED));
			label.getStyleClass().add(ProofTreeStyle.CSS_NODE_CLOSED);
		}
		else if (getItem().isLinked()) {
			setIcon(icf.getImage(IconFactory.KEY_LEAF_NODE_LINKED));
			label.getStyleClass().add(ProofTreeStyle.CSS_NODE_LINKED);
		} 
		// leaf node is an interactive node
		else if (getItem().isInteractive()) {
			setIcon(icf.getImage(IconFactory.KEY_LEAF_NODE_INTERACTIVE));
			label.getStyleClass().add(ProofTreeStyle.CSS_NODE_INTERACTIVE);
		} 
		// else: leaf node must be an open goal
		else {
			setIcon(icf.getImage(IconFactory.KEY_LEAF_NODE_OPEN));
			label.getStyleClass().add(ProofTreeStyle.CSS_NODE_OPEN);
		}
	}
}
