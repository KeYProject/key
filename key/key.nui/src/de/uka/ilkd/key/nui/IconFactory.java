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
    
    // TODO: Konstante fuer Iconname anstelle von Methode pro Icon
    // TODO: Groesse per TreeViewController Wrapper Methode oder IconFactory instanziierbar machen

	private IconFactory() {
	}

	private static String folderRoot = "components/images/TreeViewController/";

	// Inner Nodes
	private static Image keyOpenInnerNode = getImage("openNode.png");
	private static Image keyLinkedInnerNode = getImage("linkedNode.png");
	private static Image keyClosedInnerNode = getImage("closedNode.png");
	private static Image keyInteractiveInnerNode = getImage("interactiveNode.png");

	// Leafs
	private static Image keyInteractiveGoal = getImage("interactiveGoal.png");
	private static Image keyClosedGoal = getImage("closedGoal.png");
	private static Image keyOpenGoal = getImage("openGoal.png");

	/**
	 * Returns an Image based on the given imageFilename in the directory
	 * folderRoot
	 * 
	 * @param imageFilename
	 *            The name of the image
	 * @return Image object of JavaFX
	 */
	private static Image getImage(String imageFilename) {
		InputStream is = IconFactory.class.getResourceAsStream(folderRoot + imageFilename);
		return new Image(is);
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
	public static ImageView scaleIcon(Image image, int x, int y) {
		ImageView v = new ImageView(image);
		v.setFitWidth(x);
		v.setFitHeight(y);
		v.setSmooth(true);
		return v;
	}

	/**
	 * * Returns the icon scaleIcond to size (width, height) = (x, y).
	 * 
	 * @ param x the desired width of the icon @ param y the desired height of
	 * the icon
	 * 
	 * @return the scaleIcond keyOpenInnerNode
	 */
	public static ImageView getKeyOpenInnerNode(int x, int y) {
		return scaleIcon(keyOpenInnerNode, x, y);
	}

	/**
	 * Returns the icon scaleIcond to size (width, height) = (x, y).
	 * 
	 * @ param x the desired width of the icon @ param y the desired height of
	 * the icon
	 * 
	 * @return the scaleIcond keyLinkedInnerNode
	 */
	public static ImageView getKeyLinkedInnerNode(int x, int y) {
		return scaleIcon(keyLinkedInnerNode, x, y);
	}

	/**
	 * Returns the icon scaleIcond to size (width, height) = (x, y).
	 * 
	 * @ param x the desired width of the icon @ param y the desired height of
	 * the icon
	 * 
	 * @return the scaleIcond keyClosedInnerNode
	 */
	public static ImageView getKeyClosedInnerNode(int x, int y) {
		return scaleIcon(keyClosedInnerNode, x, y);
	}

	/**
	 * Returns the icon scaleIcond to size (width, height) = (x, y).
	 * 
	 * @ param x the desired width of the icon @ param y the desired height of
	 * the icon
	 * 
	 * @return the scaleIcond keyInteractiveInnerNode
	 */
	public static ImageView getKeyInteractiveInnerNode(int x, int y) {
		return scaleIcon(keyInteractiveInnerNode, x, y);
	}

	/**
	 * Returns the icon scaleIcond to size (width, height) = (x, y).
	 * 
	 * @ param x the desired width of the icon @ param y the desired height of
	 * the icon
	 * 
	 * @return the scaleIcond keyInteractiveGoal
	 */
	public static ImageView getKeyInteractiveGoal(int x, int y) {
		return scaleIcon(keyInteractiveGoal, x, y);
	}

	/**
	 * Returns the icon scaleIcond to size (width, height) = (x, y).
	 * 
	 * @ param x the desired width of the icon @ param y the desired height of
	 * the icon
	 * 
	 * @return the scaleIcond keyClosedGoal
	 */
	public static ImageView getKeyClosedGoal(int x, int y) {
		return scaleIcon(keyClosedGoal, x, y);
	}

	/**
	 * Returns the icon scaleIcond to size (width, height) = (x, y).
	 * 
	 * @ param x the desired width of the icon @ param y the desired height of
	 * the icon
	 * 
	 * @return the scaleIcond keyOpenGoal
	 */
	public static ImageView getKeyOpenGoal(int x, int y) {
		return scaleIcon(keyOpenGoal, x, y);
	}

}
