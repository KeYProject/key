package de.uka.ilkd.key.nui;

import java.io.InputStream;
import java.util.HashMap;

import javafx.scene.image.Image;
import javafx.scene.image.ImageView;

/**
 * Factory for creation of Icons shown in the proof tree.
 * 
 * @author Patrick Jattke
 *
 */
public class IconFactory {

	/**
	 * The width of produced icons in pixels.
	 */
	private final int iconSizeX;
	
	/**
	 * The height of produced icons in pixels.
	 */
	private final int iconSizeY;

	/**
	 * TODO
	 * the relative path to the root folder where icons can be found.
	 */
	private static String folderRoot = "components/images/TreeViewController/";
	
	/**
	 * An Hashmap for storing loaded icons.
	 */
	private HashMap<String, Image> icons = new HashMap<String, Image>();

	// Inner Nodes
	public final static String KEY_BRANCH_NODE_OPEN = "openBranch.png";
	public final static String KEY_BRANCH_NODE_CLOSED = "closedBranch.png";
	public final static String KEY_BRANCH_NODE_LINKED = "linkedBranch.png";
	public final static String KEY_INNER_NODE_INTERACTIVE = "interactiveNode.png";

	// Leafs
	public final static String KEY_LEAF_NODE_INTERACTIVE = "interactiveGoal.png";
	public final static String KEY_LEAF_NODE_CLOSED = "closedGoal.png";
	public final static String KEY_LEAF_NODE_OPEN = "openGoal.png";
	public final static String KEY_LEAF_NODE_LINKED = "linkedNode.png";
	
	// Context Menu
	public final static String EXPAND = "expand.png";
	public final static String COLLAPSE = "collapse.png";
	public final static String SEARCH = "search.png";
	
	/**
	 * The constructor.
	 * @param x the width of icons in pixels.
	 * @param y the height of icons in pixels.
	 */
	public IconFactory(final int x, final int y) {
		this.iconSizeX = x;
		this.iconSizeY = y;
	}

	/**
	 * Returns an ImageView (scaled image) based on the given imageFilename in
	 * the directory folderRoot
	 * If the image was demanded once before the stored image will be returned.
	 * 
	 * @param imageConstant
	 *            The name of the image, e. g. IconFactory.KEY_INNER_NODE_OPEN
	 * @return ImageView object of JavaFX
	 */
	public final ImageView getImage(final String imageConstant) {
		Image img;
		if (icons.containsKey(imageConstant)) {
			img = icons.get(imageConstant);
		} else {
			final InputStream istream = IconFactory.class.getResourceAsStream(folderRoot
					+ imageConstant);
			img = new Image(istream);
			icons.put(imageConstant, img);
		}
		return scaleIcon(img, iconSizeX, iconSizeY);
	}

	/**
	 * Scales an given image to a desired size indicated by x (width) and y
	 * (height) and returns a ImageView with the scaled image in it. Uses the
	 * smoothing option.
	 * 
	 * @param image
	 *            The image which should be scaled
	 * @param x
	 *            The desired width
	 * @param y
	 *            The desired height
	 * @return an ImageView containing the scaled Image
	 */
	private ImageView scaleIcon(final Image image, final int x, final int y) {
		final ImageView v = new ImageView(image);
		v.setFitWidth(x);
		v.setFitHeight(y);
		v.setSmooth(true);
		return v;
	}

}
