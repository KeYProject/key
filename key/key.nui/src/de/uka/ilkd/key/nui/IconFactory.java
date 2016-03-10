package de.uka.ilkd.key.nui;

import java.io.InputStream;
import java.util.HashMap;
import java.util.Map;

import javafx.scene.image.Image;
import javafx.scene.image.ImageView;

/**
 * Factory for creation of Icons shown in the proof tree.
 * 
 * @author Patrick Jattke
 * @author Matthias Schultheis
 */
public class IconFactory {

	/**
	 * The width of produced icons in pixels.
	 */
	private final int iconSizeWidth;
	
	/**
	 * The height of produced icons in pixels.
	 */
	private final int iconSizeHeight;

	/**
	 * the relative path to the root folder where icons can be found.
	 */
	private static String folderRoot = "components/images/";
	
	/**
	 * An HashMap for storing loaded icon images.
	 */
	private final Map<String, Image> icons = new HashMap<String, Image>();

	// Inner Nodes
	/** file name of open branch node icon. */
	public static final String BRANCH_OPEN = "openBranch.png";
	/** file name of closed branch node icon. */
	public static final String BRANCH_CLOSED = "closedBranch.png";
	/** file name of linked branch node icon. */
	public static final String BRANCH_LINKED = "linkedBranch.png";
	/** file name of interactive inner node icon. */
	public static final String INNER_NODE_INTERACTIVE = "interactiveNode.png";

	// Leafs
	/** file name of interactive leaf node icon. */
	public static final String LEAF_INTERACTIVE = "interactiveGoal.png";
	/** file name of closed leaf node icon. */
    public static final String LEAF_CLOSED = "closedGoalFlag.png";
    /** file name of open leaf node icon. */
    public static final String LEAF_OPEN = "openGoalFlag.png";
    /** file name of linked leaf node icon. */
	public static final String LEAF_LINKED = "linkedNode.png";
	
	// Context Menu
	/** file name of expand icon. */
	public static final String EXPAND = "expand.png";
	/** file name of collapse icon. */
	public static final String COLLAPSE = "collapse.png";
	/** file name of search icon. */
	public static final String SEARCH = "search.png";
	
	/**
	 * The constructor.
	 * @param width the width of icons in pixels.
	 * @param height the height of icons in pixels.
	 */
	public IconFactory(final int width, final int height) {
		this.iconSizeWidth = width;
		this.iconSizeHeight = height;
	}

	/**
	 * Returns an ImageView (scaled image) based on the given imageFilename in
	 * the directory folderRoot.
	 * If the image was demanded once before a stored image will be returned.
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
		return scaleIcon(img, iconSizeWidth, iconSizeHeight);
	}

	/**
	 * Scales an given image to a desired size indicated by x (width) and y
	 * (height) and returns a ImageView with the scaled image in it.
	 * 
	 * @param image
	 *            The image which should be scaled
	 * @param width
	 *            The desired width
	 * @param height
	 *            The desired height
	 * @return an ImageView containing the scaled Image
	 */
	private ImageView scaleIcon(final Image image, final int width, final int height) {
		final ImageView view = new ImageView(image);
		view.setFitWidth(width);
		view.setFitHeight(height);
		view.setSmooth(true);
		return view;
	}

}
