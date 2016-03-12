package de.uka.ilkd.key.nui.prooftree;

import java.util.ArrayList;

import de.uka.ilkd.key.nui.IconFactory;
import javafx.scene.control.Label;
import javafx.scene.image.ImageView;

/**
 * Defines for each type of NUI Node which style classes are associated with and
 * which icon image is used.
 * 
 * @author Patrick Jattke
 *
 */
public final class ProofTreeStyler {

    // the style configurations for branch nodes
    private static StyleConfiguration BRANCH_NODE_CLOSED;
    private static StyleConfiguration BRANCH_NODE_LINKED;
    private static StyleConfiguration BRANCH_NODE_OPEN;

    // the style configurations for inner nodes
    private static StyleConfiguration INNER_NODE_INTERACTIVE;

    // the style configurations for leaf nodes
    private static StyleConfiguration LEAF_NODE_CLOSED;
    private static StyleConfiguration LEAF_NODE_LINKED;
    private static StyleConfiguration LEAF_NODE_INTERACTIVE;
    private static StyleConfiguration LEAF_NODE_OPEN;

    /**
     * The icon factory to be used to get the image icons.
     */
    IconFactory icf;

    /**
     * The {@link ProofTreeCell} assigned to the current ProofTreeStyler.
     */
    ProofTreeCell ptc;

    /**
     * Bundles the name of the assigned CSS classes and the assigned icon image
     * for a specific type of node, e.g. a linked branch node. Each of these
     * configurations is a StyleConfiguration object.
     * 
     * @author Patrick Jattke
     *
     */
    public class StyleConfiguration {
        /**
         * A list of Strings, each one representing one CSS class name.
         */
        private ArrayList<String> cssClasses;
        /**
         * The assigned iconImage.
         */
        private ImageView iconImage;

        /**
         * Creates a new StyleConfiguration object.
         */
        public StyleConfiguration() {
            cssClasses = new ArrayList<String>();
            iconImage = null;
        }

        /**
         * Adds the name of a CSS class to the StyleConfiguration.
         * 
         * @param cssClass
         *            The name of the CSS class to add.
         */
        public void addCssClass(String cssClass) {
            cssClasses.add(cssClass);
        }

        /**
         * Defines the iconImage to be set to the StyleConfiguration, overwrites
         * if any iconImage was set before.
         * 
         * @param iconFileName
         *            The file name of the iconImage to set.
         */
        public void setIconImage(String iconFileName) {
            iconImage = icf.getImage(iconFileName);
            iconImage.setId(iconFileName);
        }

        /**
         * Returns the currently assigned iconImage.
         * 
         * @return {@link ImageView} containing the image.
         */
        public ImageView getIconImage() {
            return iconImage;
        }

        /**
         * Returns the list of CSS classes.
         * 
         * @return A list of Strings, each one representing one CSS class.
         */
        public ArrayList<String> getCssClasses() {
            return cssClasses;
        }

        @Override
        public boolean equals(Object sc) {
            if (sc instanceof StyleConfiguration) {
                StyleConfiguration scfg = (StyleConfiguration) sc;
                // Check existence of all CSS classes
                for (String cssClassName : getCssClasses()) {
                    if (!(scfg.getCssClasses().contains(cssClassName))) {
                        return false;
                    }
                }

                // Check if image is the same
                // First check if images are set
                if (getIconImage() != null && scfg.getIconImage() != null) {
                    // Then compare the image filename stored in ID field
                    if (!(getIconImage().getId()
                            .equals(scfg.getIconImage().getId()))) {
                        return false;
                    }
                }

                // If no condition is violated till here, both objects are equal
                return true;
            }
            // if given object is no StyleConfiguration
            return false;
        }
    } // end of class StyleConfiguration

    /**
     * Creates a new ProofTreeStyler with the ProofTreeCell ptc assigned to it.
     */
    public ProofTreeStyler(ProofTreeCell ptc) {
        this.ptc = ptc;
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
        initDefaultStyleConfigurations();
    }

    /**
     * Creates a new ProofTreeStyler without any ProofTreeCell assigned to it,
     * thus {@link #applyStyle(NUINode)} should not be called.
     */
    public ProofTreeStyler() {
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
        initDefaultStyleConfigurations();
    }

    /**
     * Initializes the default style configurations for the different types of
     * {@link NUINode}.
     */
    private void initDefaultStyleConfigurations() {
        // initialize default styles for closed branch nodes
        BRANCH_NODE_CLOSED = new StyleConfiguration();
        BRANCH_NODE_CLOSED.addCssClass(ProofTreeStyleConstants.CSS_NODE_BRANCH);
        BRANCH_NODE_CLOSED.addCssClass(ProofTreeStyleConstants.CSS_NODE_CLOSED);
        BRANCH_NODE_CLOSED.setIconImage(IconFactory.BRANCH_CLOSED);

        // initialize default styles for linked branch nodes
        BRANCH_NODE_LINKED = new StyleConfiguration();
        BRANCH_NODE_LINKED.addCssClass(ProofTreeStyleConstants.CSS_NODE_BRANCH);
        BRANCH_NODE_LINKED.addCssClass(ProofTreeStyleConstants.CSS_NODE_LINKED);
        BRANCH_NODE_LINKED.setIconImage(IconFactory.BRANCH_LINKED);

        // initialize default styles for open branch nodes
        BRANCH_NODE_OPEN = new StyleConfiguration();
        BRANCH_NODE_OPEN.addCssClass(ProofTreeStyleConstants.CSS_NODE_BRANCH);
        BRANCH_NODE_OPEN.addCssClass(ProofTreeStyleConstants.CSS_NODE_OPEN);
        BRANCH_NODE_OPEN.setIconImage(IconFactory.BRANCH_OPEN);

        // initialize default styles for interactive inner nodes
        INNER_NODE_INTERACTIVE = new StyleConfiguration();
        INNER_NODE_INTERACTIVE.setIconImage(IconFactory.INNER_NODE_INTERACTIVE);

        // initialize default styles for closed leaf nodes
        LEAF_NODE_CLOSED = new StyleConfiguration();
        LEAF_NODE_CLOSED.addCssClass(ProofTreeStyleConstants.CSS_NODE_CLOSED);
        LEAF_NODE_CLOSED.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        LEAF_NODE_CLOSED.setIconImage(IconFactory.LEAF_CLOSED);

        // initialize default styles for linked leaf nodes
        LEAF_NODE_LINKED = new StyleConfiguration();
        LEAF_NODE_LINKED.addCssClass(ProofTreeStyleConstants.CSS_NODE_LINKED);
        LEAF_NODE_LINKED.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        LEAF_NODE_LINKED.setIconImage(IconFactory.LEAF_LINKED);

        // initialize default styles for interactive leaf nodes
        LEAF_NODE_INTERACTIVE = new StyleConfiguration();
        LEAF_NODE_INTERACTIVE
                .addCssClass(ProofTreeStyleConstants.CSS_NODE_INTERACTIVE);
        LEAF_NODE_INTERACTIVE
                .addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        LEAF_NODE_INTERACTIVE.setIconImage(IconFactory.LEAF_INTERACTIVE);

        // initialize default styles for open leaf nodes
        LEAF_NODE_OPEN = new StyleConfiguration();
        LEAF_NODE_OPEN.addCssClass(ProofTreeStyleConstants.CSS_NODE_OPEN);
        LEAF_NODE_OPEN.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        LEAF_NODE_OPEN.setIconImage(IconFactory.LEAF_OPEN);
    }

    /**
     * Applies the {@link StyleConfiguration} determined by
     * {@link #getStyleConfiguration(NUINode)} to the given node.
     * 
     * @param node
     *            The node where the StyleConfiguration should be applied to.
     */
    public void applyStyle(NUINode node) {
        Label label = ptc.getLabel();

        StyleConfiguration scfg = node.getStyleConfiguration();

        // Apply CSS classes
        ArrayList<String> cssClasses = scfg.getCssClasses();
        for (String cssClass : cssClasses) {
            label.getStyleClass().add(cssClass);
        }

        // Apply icon image
        ImageView image = scfg.getIconImage();
        if (image != null) {
            ptc.setIcon(image);
        }
    }

    /**
     * Returns the matching {@link StyleConfiguration} for the given type of
     * {@link NUINode}.
     * 
     * @param node
     *            The node whose StyleConfiguration should be determined.
     * @return StyleConfiguration of the given node.
     */
    public StyleConfiguration getStyleConfiguration(NUINode node) {
        // if the node is branch node
        if (node instanceof NUIBranchNode) {
            if (node.isClosed()) {
                return BRANCH_NODE_CLOSED;
            }
            else if (node.isLinked()) {
                return BRANCH_NODE_LINKED;
            }
            else {
                return BRANCH_NODE_OPEN;
            }
        }
        // if the node is a leaf node
        else if (node instanceof NUILeafNode) {
            if (node.isClosed()) {
                return LEAF_NODE_CLOSED;
            }
            else if (node.isLinked()) {
                return LEAF_NODE_LINKED;
            }
            else if (node.isInteractive()) {
                return LEAF_NODE_INTERACTIVE;
            }
            else {
                return LEAF_NODE_OPEN;
            }
        }
        // if the node is an inner node
        else {
            if (node.isInteractive()) {
                return INNER_NODE_INTERACTIVE;
            }
        }

        // otherwise an empty style configuration is returned
        return new StyleConfiguration();
    }

}
