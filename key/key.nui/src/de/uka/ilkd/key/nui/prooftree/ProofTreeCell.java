package de.uka.ilkd.key.nui.prooftree;

import de.uka.ilkd.key.nui.IconFactory;
import javafx.scene.control.Label;
import javafx.scene.control.TreeCell;
import javafx.scene.image.ImageView;
import javafx.scene.layout.HBox;

/**
 * This class is responsible for the rendering of a tree cell.
 * @author  Matthias Schultheis
 * @version 1.0
 */
public class ProofTreeCell extends TreeCell<NUINode> {
	
    /**
     * the icon size in px
     */
    private final int ICON_SIZE = 15;
    
    /**
     * space between icon and label in px
     */
    private final int ICON_SPACING = 5;
        
    /**
     * the label that will be displayed
     */
	private Label label;

    /**
     * The IconFactory used to create the required icons
     */
    private IconFactory icf;
    
    /**
     * the icon that will be displayed left next to the label
     */
	private ImageView icon;
	
	/**
	 * The constructor of the ProofTreeCell
	 */
	public ProofTreeCell() {
		icf = new IconFactory(ICON_SIZE, ICON_SIZE);
	}
	
	/**
	 * @param icon the icon to set
	 */
	private void setIcon(ImageView icon) {
		this.icon = icon;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	protected void updateItem(NUINode item, boolean empty) {
		super.updateItem(item, empty);
		
		setContextMenu(new ProofTreeContextMenu(item, getTreeItem()));
		
		// if null node, display nothing
		if(item == null) {
			setText(null);
			setGraphic(null);
			return;
		}
		
		// reset label and icon
	    label = new Label(item.getLabel()+" ");
	    icon  = null;
        
	    
	    
        // set decoration (style, icon)
		if(item instanceof NUIInnerNode)
			decorateAsInnerNode();
		else if(item instanceof NUIBranchNode)
			decorateAsBranchNode();
		else if(item instanceof NUILeafNode)
			decorateAsLeafNode();
        
		// workaround to display an icon next to a label
		setText(null);
		if(icon != null) {
		    HBox hbox = new HBox();
		    hbox.setSpacing(ICON_SPACING);
		    
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
			setIcon(icf.getImage(IconFactory.KEY_INNER_NODE_CLOSED));
		} else {
			if (getItem().isLinked()) {
				setIcon(icf.getImage(IconFactory.KEY_INNER_NODE_LINKED));
			} else {
				setIcon(icf.getImage(IconFactory.KEY_INNER_NODE_OPEN));
			}
			
			
		}
		// TODO: Implement logic for linked (non-leaf) Nodes
		// Not here but instead in the converter!!!
		// see ProofTreeView (line 712-735)
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
		// leaf node is a linked node
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
