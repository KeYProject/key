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
 * @author Stefan Pilot
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
    private static StyleConfiguration innerNdeInteractv;

    /**
     * Style for closed leaf nodes.
     */
    private static StyleConfiguration leafNodeClosed;

    /**
     * Style for interactive leaf nodes.
     */
    private static StyleConfiguration leafNodeInteractv;

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
     * Bundles the name of the assigned CSS classes and the assigned icon image
     * for a specific type of node, e.g. a linked branch node. Each of these
     * configurations is a StyleConfiguration object.
     * 
     * @author Patrick Jattke
     * @author Stefan Pilot
     *
     */
    @SuppressWarnings("PMD.OverrideBothEqualsAndHashcode") // it's useless. It really is.
    public class StyleConfiguration {
        /**
         * A list of Strings, each one representing one CSS class name.
         */
        private final List<String> cssClasses;
        /**
         * See hashCode().
         */
        private final int HASH_CODE = 5;
        /**
         * The name of the assigned iconImage.
         */
        private String iconImage;

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
        public boolean equals(final Object obj) {

            return obj instanceof StyleConfiguration && !(

            // Check existence of all CSS classes
            getCssClasses().stream()
                    .anyMatch((item) -> !((StyleConfiguration) obj).getCssClasses().contains(item))

                    || (// Check if image is the same

            // First check if images are set
            // NOPMD Justification: These parentheses are not useless.
            getIconImage() != null && ((StyleConfiguration) obj).getIconImage() != null // NOPMD
            // Then compare the image filename stored in ID field
                    && !(getIconImage().getId()
                            .equals(((StyleConfiguration) obj).getIconImage().getId()))));
        }

        /**
         * This method is definitely and absolutely neccessary and does serve
         * many purposes besides satisfying FindBugs and PMD.
         */
        @Override
        public int hashCode() {
            return HASH_CODE; // Guaranteed to be a collision-free hash, see
                      // https://xkcd.com/221/
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
            if (this.iconImage == null) {
                return null;
            }
            final ImageView img = icf.getImage(iconImage);
            img.setId(iconImage);
            return img;
        }

        /**
         * Defines the iconImage to be set to the StyleConfiguration, overwrites
         * if any iconImage was set before.
         * 
         * @param iconFileName
         *            The file name of the iconImage to set.
         */
        public void setIconImage(final String iconFileName) {
            this.iconImage = iconFileName;
        }
    } // end of class StyleConfiguration

    /**
     * Creates a new ProofTreeStyler without any ProofTreeCell assigned to it,
     * thus {@link #applyStyle(NUINode)} should not be called.
     */
    public ProofTreeStyler() {
        this.icf = new IconFactory(ProofTreeCell.ICON_SIZE, ProofTreeCell.ICON_SIZE);
        initDefaultStyleConfigurations();
    }

    /**
     * Creates a new ProofTreeStyler with the ProofTreeCell ptc assigned to it.
     * * @param ptc The {@link ProofTreeCell} associated with this
     * ProofTreeStyler.
     */

    /**
     * Applies the {@link StyleConfiguration} determined by
     * {@link #getStyleConfiguration(NUINode)} to the given node.
     * 
     * @param node
     *            The node where the StyleConfiguration should be applied to.
     * @param ptc
     *            The ProofTreeCell containing the node.
     */
    public static void applyStyle(final NUINode node, final ProofTreeCell ptc) {
        final Label label = ptc.getLabel();

        final StyleConfiguration scfg = node.getStyleConfiguration();

        // Apply CSS classes

        final List<String> cssClasses = scfg.getCssClasses();

        cssClasses.forEach(cssClass -> label.getStyleClass().add(cssClass));

        // Apply icon image
        ptc.setIcon(scfg.getIconImage());

    }

    /**
     * Getter.
     * 
     * @return the {@link IconFactory}.
     */
    public IconFactory getIcf() {
        return icf;
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
    @SuppressWarnings("PMD.CyclomaticComplexity") // this routine is actually quite simple
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
                return leafNodeInteractv;
            }
            else {
                return leafNodeOpen;
            }
        }
        // if the node is an inner node
        else if (node instanceof NUIInnerNode && node.isInteractive()) {
            return innerNdeInteractv;
        }

        // otherwise an empty style configuration is returned
        return new StyleConfiguration();
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
        innerNdeInteractv = new StyleConfiguration();
        innerNdeInteractv.setIconImage(IconFactory.INNER_INTERACTIVE);

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
        leafNodeInteractv = new StyleConfiguration();
        leafNodeInteractv.addCssClass(ProofTreeStyleConstants.CSS_NODE_NTRACTV);
        leafNodeInteractv.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        leafNodeInteractv.setIconImage(IconFactory.LEAF_INTERACTIVE);

        // initialize default styles for open leaf nodes
        leafNodeOpen = new StyleConfiguration();
        leafNodeOpen.addCssClass(ProofTreeStyleConstants.CSS_NODE_OPEN);
        leafNodeOpen.addCssClass(ProofTreeStyleConstants.CSS_NODE_LEAF);
        leafNodeOpen.setIconImage(IconFactory.LEAF_OPEN);
    }
}
