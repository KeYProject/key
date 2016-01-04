package de.uka.ilkd.key.nui;

import java.io.InputStream;

import javafx.scene.image.Image;
import javafx.scene.image.ImageView;

/**
 * Factory for creation of Icons shown in the proof tree.
 * 
 * @author Patrick Jattke
 *
 */
public class IconFactory {

	private int iconSize_x;
	private int iconSize_y;

	public IconFactory(int x, int y) {
		this.iconSize_x = x;
		this.iconSize_y = y;
	}

	private static String folderRoot = "components/images/TreeViewController/";

	// Inner Nodes
	public static String KEY_INNER_NODE_OPEN = "openNode.png";
	public static String KEY_INNER_NODE_CLOSED = "closedNode.png";
	public static String KEY_INNER_NODE_LINKED = "linkedNode.png";
	public static String KEY_INNER_NODE_INTERACTIVE = "interactiveNode.png";

	// Leafs
	public static String KEY_LEAF_NODE_INTERACTIVE = "interactiveGoal.png";
	public static String KEY_LEAF_NODE_CLOSED = "closedGoal.png";
	public static String KEY_LEAF_NODE_OPEN = "openGoal.png";
	public static String KEY_LEAF_NODE_LINKED = "linkedNode.png";

	/**
	 * Returns an ImageView (scaled image) based on the given imageFilename in
	 * the directory folderRoot
	 * 
	 * @param imageConstant
	 *            The name of the image, e. g. IconFactory.KEY_INNER_NODE_OPEN
	 * @return ImageView object of JavaFX
	 */
	public ImageView getImage(String imageConstant) {
		InputStream is = IconFactory.class.getResourceAsStream(folderRoot + imageConstant);
		Image img = new Image(is);
		return scaleIcon(img, iconSize_x, iconSize_y);
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
	private ImageView scaleIcon(Image image, int x, int y) {
		ImageView v = new ImageView(image);
		v.setFitWidth(x);
		v.setFitHeight(y);
		v.setSmooth(true);
		return v;
	}

}
