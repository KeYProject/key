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

	private IconFactory() {
	}
	
	private static String folderRoot = "components/images/";
	private static Image keyHole = getImage("ekey-mono.png");
	private static Image keyHoleClosed = getImage("keyproved.png");
	private static Image keyFolderBlue = getImage("folder-blue.png");
	private static Image keyFolderGray = getImage("folder-gray.png");

	/**
	 * Returns an Image based on the given imageFilename in the directory folderRoot
	 * 
	 * @param imageFilename
	 * 				The name of the image
	 * @return Image object of JavaFX
	 */
	private static Image getImage(String imageFilename) {
		InputStream is = IconFactory.class.getResourceAsStream(folderRoot + imageFilename);
		return new Image(is);
	}

	/**
	 * Scales an given image to a desired size indicated by x (width) and y (height) and 
	 * returns a ImageView with the scaled image in it. Uses the smoothing option.
	 * 
	 * @param image
	 * 			The image which should be scaled
	 * @param x
	 * 			The desired width
	 * @param y
	 * 			The desired height
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
	 * Returns the image keyHole scaled to the given size, 
	 * where x indicates the width and y the height.
	 * 
	 * @param x The desired width of the image
	 * @param y The desired height of the image
	 * @return an ImageView object containing the scaled image
	 */
	public static ImageView keyHole(int x, int y) {
		return scaleIcon(keyHole, x, y);
	}

	/**
	 * Returns the image keyHoleClosed scaled to the given size, 
	 * where x indicates the width and y the height.
	 * 
	 * @param x The desired width of the image
	 * @param y The desired height of the image
	 * @return an ImageView object containing the scaled image
	 */
	public static ImageView keyHoleClosed(int x, int y) {
		return scaleIcon(keyHoleClosed, x, y);
	}

	/**
	 * Returns the image keyFolderBlue scaled to the given size, 
	 * where x indicates the width and y the height.
	 * 
	 * @param x The desired width of the image
	 * @param y The desired height of the image
	 * @return an ImageView object containing the scaled image
	 */
	public static ImageView keyFolderBlue(int x, int y) {
		return scaleIcon(keyFolderBlue, x, y);
	}
	
	/**
	 * Returns the image keyFolderGray scaled to the given size, 
	 * where x indicates the width and y the height.
	 * 
	 * @param x The desired width of the image
	 * @param y The desired height of the image
	 * @return an ImageView object containing the scaled image
	 */
	public static ImageView keyFolderGray(int x, int y) {
		return scaleIcon(keyFolderGray, x, y);
	}
}
