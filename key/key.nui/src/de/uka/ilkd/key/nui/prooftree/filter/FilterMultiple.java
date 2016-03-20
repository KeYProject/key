package de.uka.ilkd.key.nui.prooftree.filter;

import java.util.LinkedList;
import java.util.List;
import java.util.function.Predicate;
import de.uka.ilkd.key.nui.prooftree.NUINode;

/**
 * A filter that can be used to combine multiple filters via AND.
 * 
 * @author Matthias Schultheis
 */
public class FilterMultiple implements ProofTreeFilter {

    /**
     * The list of filers that are combined.
     */
    private List<ProofTreeFilter> filters = new LinkedList<>();

    @Override
    public boolean test(final NUINode node) {
        for (final Predicate<NUINode> filter : filters) {
            if (!filter.test(node)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Adds a filter to the combination.
     * 
     * @param filter
     *            The filter to add.
     */
    public void addFilter(final ProofTreeFilter filter) {
        filters.add(filter);
    }

    /**
     * Sets all the list of filters.
     * 
     * @param filters
     *            The list of filters.
     */
    public void setAllFilters(final List<ProofTreeFilter> filters) {
        this.filters = filters;
    }

    /**
     * Removes all currently loaded filters.
     */
    public void clear() {
        this.filters.clear();
    }

    @Override
    public String getContextMenuItemText() {
        return "";
    }
}
