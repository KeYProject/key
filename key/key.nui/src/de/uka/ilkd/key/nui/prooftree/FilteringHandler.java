package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import de.uka.ilkd.key.nui.prooftree.filter.FilterShowAll;
import de.uka.ilkd.key.nui.prooftree.filter.FilterCombineAND;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideClosed;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideIntermediate;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideNonInteractive;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;

/**
 * Handles the filtering of the proof tree.
 * @author Matthias Schultheis
 *
 */
public class FilteringHandler {
    
    /**
     * A map storing filters with their resp. activation flag.
     */
    private Map<ProofTreeFilter, Boolean> filtersMap = new LinkedHashMap<>();
    
    //TODO replace
    ProofTreeItem root;
    
    /**
     * Constructor.
     */
    public FilteringHandler() {
        
        final List<ProofTreeFilter> filters = searchFilterClasses();
        filters.forEach((filter) -> filtersMap.put(filter, false));
    }
    
    /**
     * Searches for applicable filters in the package
     * de.uka.ilkd.key.nui.prooftree.filter.
     * @return A list of filters
     */
    private List<ProofTreeFilter> searchFilterClasses() {
        
        final List<ProofTreeFilter> filters = new LinkedList<ProofTreeFilter>();
        
        //TODO search in package
        filters.add(new FilterHideClosed());
        filters.add(new FilterHideIntermediate());
        filters.add(new FilterHideNonInteractive());
        
        return filters;
    }
    
    /**
     * Returns a list of the currently active filters.
     * @return A list of the currently active filters.
     */
    private List<ProofTreeFilter> getActiveFilters() {
        
        final List<ProofTreeFilter> filters = new LinkedList<ProofTreeFilter>();

        filtersMap.forEach((filter, active) -> {
            if (active) {
                filters.add(filter);
            }
        });
        
        return filters;
    }
    
    /**
     * Applies the filters that are currently set to active.
     */
    private void applyFilters() {
        final List<ProofTreeFilter> activeFilters = getActiveFilters();

        // reduces all active filers to one
        final ProofTreeFilter redFilter = activeFilters.stream().reduce(new FilterShowAll(),
                (f1, f2) -> {
                    return new FilterCombineAND(f1, f2);
                });

        //TODO perform filtering to current visible tree
        root.filter(redFilter);
    }

    /**
     * @return the filtersMap
     */
    public Map<ProofTreeFilter, Boolean> getFiltersMap() {
        return filtersMap;
    }

    /**
     * Returns the activation status for a filter.
     * @param filter The filter to check
     * @return true iff the filter is activated
     */
    public boolean getFilterStatus(final ProofTreeFilter filter) {
        return filtersMap.get(filter);
    }
    
    /**
     * Toggles the activation status for a filter.
     * @param filter The filter to change the status of.
     */
    public void toggleFilteringStatus(final ProofTreeFilter filter) {
        final boolean newState = !filtersMap.get(filter);
        filtersMap.put(filter, newState);
        
        applyFilters();
    }
    
    //TODO replace
    @Deprecated
    public void setTree(ProofTreeItem r) {
        root = r;
    }
    
}
