package de.uka.ilkd.key.nui.prooftree.filter;

import java.util.function.Predicate;

import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * An interface for all proof tree filters.
 * 
 * @author Matthias Schultheis
 *
 */
public interface ProofTreeFilter extends Predicate<NUINode> {

    /**
     * Delivers the label text to display the filter item in the context menu.
     * 
     * @return The context menu item text
     */
    String getContextMenuItemText();
}