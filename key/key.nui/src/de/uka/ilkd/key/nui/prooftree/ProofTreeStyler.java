package de.uka.ilkd.key.nui.prooftree;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.nui.IconFactory;
import javafx.scene.control.Label;
import javafx.scene.image.ImageView;

/**
 * Defines for each type of NUI Node which style classes are associated with and
 * which icon image is used. For example for closed branch nodes, linked inner
 * nodes etc.
 * 
 * @author Patrick Jattke
 *
 */
public final class ProofTreeStyler {

    /**
     * Style for closed branch nodes.
     */
    private static StyleConfiguration branchNodeClosed;

    /**
     * Style for linked branch nodes.
     */
    private static StyleConfiguration branchNodeLinked;

    /**
     * Style for open branch nodes.
     */
    private static StyleConfiguration branchNodeOpen;

    /**
     * Style for interactive inner nodes.
     */
    private static StyleConfiguration innerNodeInteractive;

    /**
     * Style for closed leaf nodes.
     */
    private static StyleConfiguration leafNodeClosed;

    /**
     * Style for interactive leaf nodes.
     */
    private static StyleConfiguration leafNodeInteractive;

    /**
     * Style for linked leaf nodes.
     */
    private static StyleConfiguration leafNodeLinked;

    /**
     * Style for open leaf nodes.
     */
    private static StyleConfiguration leafNodeOpen;

    /**
     * The icon factory to be used to get the image icons.
     */
    private final IconFactory icf;
    /**
     * The {@link ProofTreeCell} assigned to the current ProofTreeStyler.
     */
    private ProofTreeCell ptc;

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
        private final List<String> cssClasses;
        /**
         * The assigned iconImage.
         */
        private ImageView iconImage;

        /**
         * Creates a new StyleConfiguration object.
         */
        public StyleConfiguration() {
            cssClasses = new ArrayList<>();
        }

        /**
         * Adds the name of a CSS class to the StyleConfiguration.
         * 
         * @param cssClass
         *            The name of the CSS class to add.
         */
        public void addCssClass(final String cssClass) {
            cssClasses.add(cssClass);
        }


        @Override
        public boolean equals(Object obj) {

            return obj instanceof StyleConfiguration && !(

            // Check existence of all CSS classes
            getCssClasses().stream()
                    .anyMatch((item) -> !((StyleConfiguration) obj).getCssClasses().contains(item))

                    || ( // Check if image is the same

            // First check if images are set
            getIconImage() != null && ((StyleConfiguration) obj).getIconImage() != null
            // Then compare the image filename stored in ID field
                    && !(getIconImage().getId()
                            .equals(((StyleConfiguration) obj).getIconImage().getId()))));
        }

        /**
         * Returns the list of CSS classes.
         * 
         * @return A list of Strings, each one representing one CSS class.
         */
        public List<String> getCssClasses() {
            return cssClasses;
        }

        /**
         * Returns the currently assigned iconImage.
         * 
         * @return {@link ImageView} containing the image.
         */
        public ImageView getIconImage() {
            return iconImage;
        }

        @Override
        public int hashCode() {
            final int prime = 31;
            int result = 1;
            result = prime * result + getOuterType().hashCode();
            result = prime * result + ((cssClasses == null) ? 0 : cssClasses.hashCode());
            result = prime * result + ((iconImage == null) ? 0 : iconImage.hashCode());
            return result;
        }


        /**
         * Defines the iconImage to be set to the StyleConfiguration, overwrites
         * if any iconImage was set before.
         * 
         * @param iconFileName
         *            The file name of the iconImage to set.
         */
        public void setIconImage(final String iconFileName) {
            iconImage = icf.getImage(iconFileName);
            iconImage.setId(iconFileName);
        }

        /**
         * Returns the outer, enclosing instance if the class is an inner class
         * (non-static nested class).
         * 
         * @return The outer, enclosing instance, iff the class is an non-static
         *         nested class.
         */
        private ProofTreeStyler getOuterType() {
            return ProofTreeStyler.this;
        }

    } // end of class StyleConfiguration

    /**
     * Creates a new ProofTreeStyler without any ProofTreeCell assigned to it,
     * thus {@link #applyStyle(NUINode)} should not be called.
     */
    public ProofTreeStyler() {
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
        initDefaultStyleConfigurations();
    }

    /**
     * Creates a new ProofTreeStyler with the ProofTreeCell ptc assigned to it.
     * * @param ptc
     *            The {@link ProofTreeCell} associated with this
     *            ProofTreeStyler.
     */
    public ProofTreeStyler(final ProofTreeCell ptc) {
        this.ptc = ptc;
        icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
        initDefaultStyleConfigurations();
    }

    /**
     * Applies the {@link StyleConfiguration} determined by
     * {@link #getStyleConfiguration(NUINode)} to the given node.
     * 
     * @param node
     *            The node where the StyleConfiguration should be applied to.
     */
    public void applyStyle(final NUINode node) {
        final Label label = ptc.getLabel();

        final StyleConfiguration scfg = node.getStyleConfiguration();

        // Apply CSS classes

        final List<String> cssClasses = scfg.getCssClasses();

        cssClasses.forEach(cssClass -> label.getStyleClass().add(cssClass));

        // Apply icon image
        final ImageView image = scfg.getIconImage();
        if (image != null) {
            ptc.setIcon(image);
        }
    }

    /**
     * TODO
     * 
     * @return
     */
    public IconFactory getIcf() {
        return icf;
    }

    /**
     * TODO
     * 
     * @return
     */
    public ProofTreeCell getPtc() {
        return ptc;
    }

    /**
     * Returns the matching {@link StyleConfiguration} for the given type of
     * {@link NUINode}. If no type matches, an empty StyleConfiguration is
     * returned.
     * 
     * @param node
     *            The node whose StyleConfiguration should be determined.
     * @return StyleConfiguration of the given node.
     */
    public StyleConfiguration getStyleConfiguration(final NUINode node) {
        // if the node is branch node
        if (node instanceof NUIBranchNode) {
            if (node.isClosed()) {
                return branchNodeClosed;
            }
            else if (node.isLinked()) {
                return branchNodeLinked;
            }
            else {
                return branchNodeOpen;
            }
        }
        // if the node is a leaf node
        else if (node instanceof NUILeafNode) {
            if (node.isClosed()) {
                return leafNodeClosed;
            }
            else if (node.isLinked()) {
                return leafNodeLinked;
            }
            else if (node.isInteractive()) {
                return leafNodeInteractive;
            }
            else {
                return leafNodeOpen;
            }
        }
        // if the node is an inner node
        else if (node instanceof NUIInnerNode && node.isInteractive()) {
            return innerNodeInteractive;
        }

        // otherwise an empty style configuration is returned
        return new StyleConfiguration();
    }

    /**
     * TODO
     * 
     * @param ptc
     */
    public void setPtc(final ProofTreeCell ptc) {
        this.ptc = ptc;
    }

    /**
     * Initializes the default style configurations for the different types of
     * {@link NUINode}.
     */
    private void initDefaultStyleConfigurations() {
        // initialize default styles for closed branch nodes
        branchNodeClosed = new StyleConfiguration();
        branchNodeClosed.addCssClass(ProofTreeStyleConstants.CSS_NODE_BRANCH);
        branchNodeClosed.addCssClass(ProofTreeStyleConstants.CSS_NODE_CLOSED);
        branchNodeClosed.setIconImage(IconFactory.BRANCH_CLOSED);

        // initialize default styles for linked branch nodes
        branchNodeLinked = new StyleConfiguration();
        branchNodeLinked.addCssClass(ProofTreeStyleConstants.CSS_NODE_BRANCH);
        branchNodeLinked.addCssClass(ProofTreeStyleConstants.CSS_NODE_LINKED);
        branchNodeLinked.setIconImage(IconFactory.BRANCH_LINKED);

        // initialize default styles for open branch nodes
        branchNodeOpen = new StyleConfiguration();
        branchNodeOpen.addCssClass(ProofTreeStyleConstants.CSS_NODE_BRANCH);
        branchNodeOpen.addCssClass(ProofTreeStyleConstants.CSS_NODE_OPEN);
        branchNodeOpen.setIconImage(IconFactory.BRANCH_OPEN);

        // initialize default styles for interactive inner nodes
        innerNodeInteractive = new StyleConfiguration();
        innerNodeInteractive.setIconImage(IconFactory.INNER_INTERACTIVE);

        // initialize default styles for closed leaf nodes
        leafNodeClosed = new StyleConfiguration();
        leafNodeClosed.addCssClass(ProofTreeStyleConstants.CSS_NODE_CLOSED);
        leafNodeClosed.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        leafNodeClosed.setIconImage(IconFactory.LEAF_CLOSED);

        // initialize default styles for linked leaf nodes
        leafNodeLinked = new StyleConfiguration();
        leafNodeLinked.addCssClass(ProofTreeStyleConstants.CSS_NODE_LINKED);
        leafNodeLinked.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        leafNodeLinked.setIconImage(IconFactory.LEAF_LINKED);

        // initialize default styles for interactive leaf nodes
        leafNodeInteractive = new StyleConfiguration();
        leafNodeInteractive.addCssClass(ProofTreeStyleConstants.CSS_NODE_INTERACTIVE);
        leafNodeInteractive.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        leafNodeInteractive.setIconImage(IconFactory.LEAF_INTERACTIVE);

        // initialize default styles for open leaf nodes
        leafNodeOpen = new StyleConfiguration();
        leafNodeOpen.addCssClass(ProofTreeStyleConstants.CSS_NODE_OPEN);
        leafNodeOpen.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        leafNodeOpen.setIconImage(IconFactory.LEAF_OPEN);
    }

}
