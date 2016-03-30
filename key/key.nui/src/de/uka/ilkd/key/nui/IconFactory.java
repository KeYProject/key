package de.uka.ilkd.key.nui;

import java.io.File;
import java.util.HashMap;
import java.util.Map;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;

/**
 * Factory for creation of Icons shown in the proof tree.
 * 
 * @author Patrick Jattke
 * @author Matthias Schultheis
 * @author Stefan Pilot
 */
public class IconFactory {
    /**
     * the relative path to the root folder where icons can be found.
     */
    private static String folderRoot = "components/images/";

    // Main Window
    /**
     * File name of the icon used in the cancel button of the MainViewController.
     */
    public static final String CANCEL_BUTTON = "images/cancelButton.png";

    // Branch Nodes
    /** file name of closed branch node icon. */
    public static final String BRANCH_CLOSED = folderRoot + "closedBranch.png";

    /** file name of linked branch node icon. */
    public static final String BRANCH_LINKED = folderRoot + "linkedBranch.png";

    // Inner Nodes
    /** file name of open branch node icon. */
    public static final String BRANCH_OPEN = folderRoot + "openBranch.png";

    /** file name of collapse icon. */
    public static final String COLLAPSE = folderRoot + "collapse.png";

    // Context Menu
    /** file name of expand icon. */
    public static final String EXPAND = folderRoot + "expand.png";

    // StrategyView
    /** file name of goButton icon. */
    public static final String GO_BUTTON = folderRoot + "goButton.png";

    /** file name of interactive inner node icon. */
    public static final String INNER_INTERACTIVE = folderRoot
            + "interactiveNode.png";

    /** file name of closed leaf node icon. */
    public static final String LEAF_CLOSED = folderRoot + "closedGoalFlag.png";
    // Leafs
    /** file name of interactive leaf node icon. */
    public static final String LEAF_INTERACTIVE = folderRoot
            + "interactiveGoal.png";
    /** file name of linked leaf node icon. */
    public static final String LEAF_LINKED = folderRoot + "linkedNode.png";
    /** file name of open leaf node icon. */
    public static final String LEAF_OPEN = folderRoot + "openGoalFlag.png";

    /** file name of search icon. */
    public static final String SEARCH = folderRoot + "search.png";
    /**
     * An HashMap for storing loaded icon images.
     */
    private final Map<String, Image> icons = new HashMap<>(); //NOPMD -- thread safety not needed

    /**
     * The height of produced icons in pixels.
     */
    private final int iconSizeHeight;
    /**
     * The width of produced icons in pixels.
     */
    private final int iconSizeWidth;

    /**
     * A Field that indicates whether or not this IconFactory thinks it is run from a JAR file.
     */
    @SuppressWarnings({ "PMD.AvoidFieldNameMatchingMethodName", "PMD.BeanMembersShouldSerialize" })
    // PMD Justification: a) Styleguide wants this b) We found a bug in PMD here
    private final boolean isRunFromJAR;

    /**
     * The constructor.
     *
     * @param width
     *            the width of icons in pixels.
     * @param height
     *            the height of icons in pixels.
     */
    public IconFactory(final int width, final int height) {
        this.iconSizeWidth = width;
        this.iconSizeHeight = height;
        final File jarFile = new File(
                getClass().getProtectionDomain().getCodeSource().getLocation().getPath());
        this.isRunFromJAR = jarFile.isFile();
    }

    /**
     * Getter.
     *
     * @return a {@link Map}&lt;{@link String}, {@link Image}&gt;
     */
    public Map<String, Image> getIcons() {
        return icons;
    }

    /**
     * Getter.
     *
     * @return an int representing the heigth of an item.
     */
    public int getIconSizeHeight() {
        return iconSizeHeight;
    }

    /**
     * Getter.
     *
     * @return an int representing the width of an icon.
     */
    public int getIconSizeWidth() {
        return iconSizeWidth;
    }

    /**
     * Getter.
     * @return true if this IconFactory thinks it is being run from a JAR file.
     */
    public boolean isRunFromJAR() {
        return isRunFromJAR;
    }

    /**
     * Returns an ImageView (scaled image) based on the given imageFilename in
     * the directory folderRoot. If the image was demanded once before a stored
     * image will be returned.
     *
     * @param imageConstant
     *            The name of the image, e. g. IconFactory.KEY_INNER_NODE_OPEN
     * @return ImageView object of JavaFX
     */
    public final ImageView getImage(final String imageConstant) {
        final Image img; //NOPMD this makes no sense as a field.
        if (icons.containsKey(imageConstant)) {
            img = icons.get(imageConstant);
        }
        else {
            if (isRunFromJAR) {
               img = new Image("/de/uka/ilkd/key/nui/" + imageConstant, iconSizeWidth,
                        iconSizeHeight, false, false);
            }
            else {
                img = new Image(getClass().getResourceAsStream(imageConstant), iconSizeWidth,
                        iconSizeHeight, false, false);
            }
            icons.put(imageConstant, img);
        }
        return new ImageView(img);
    }
}
