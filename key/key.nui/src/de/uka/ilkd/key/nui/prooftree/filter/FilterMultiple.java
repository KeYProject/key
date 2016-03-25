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
@SuppressWarnings("PMD.AtLeastOneConstructor")
//PMD will also complain if adding the constructor, then saying "avoid useless constructors"
public class FilterMultiple implements ProofTreeFilter {

    /**
     * The list of filers that are combined.
     */
    private List<ProofTreeFilter> filters = new LinkedList<>();

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
     * Removes all currently loaded filters.
     */
    public void clear() {
        this.filters.clear();
    }

    @Override
    public String getContextMenuItemText() {
        return "";
    }

    /**
     * Getter.
     * @return a {@link List}&lt;{@link ProofTreeFilter}&gt; containing all the filters.
     */
    public List<ProofTreeFilter> getFilters() {
        return filters;
    }

    /**
     * Sets all the list of filters.
     * 
     * @param filters
     *            The list of filters.
     */
    public void setFilters(final List<ProofTreeFilter> filters) {
        this.filters = filters;
    }

    @Override
    @SuppressWarnings("PMD.JUnit4TestShouldUseTestAnnotation")
    public boolean test(final NUINode node) {
        for (final Predicate<NUINode> filter : filters) {
            if (!filter.test(node)) {
                return false;
            }
        }
        return true;
    }
}
