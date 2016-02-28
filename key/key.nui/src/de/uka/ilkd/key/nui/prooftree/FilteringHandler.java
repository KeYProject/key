package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedHashMap;
import java.util.Map;
import de.uka.ilkd.key.nui.prooftree.filter.FilterShowAll;
import de.uka.ilkd.key.nui.prooftree.filter.FilterHideClosed;
import de.uka.ilkd.key.nui.prooftree.filter.ProofTreeFilter;

/**
 * Handles the filtering of the proof tree.
 * @author Matthias Schultheis
 *
 */
public class FilteringHandler {
    
    private Map<ProofTreeFilter, Boolean> filtersMap = new LinkedHashMap<>();
    ProofTreeItem root;
    
    
    public FilteringHandler() {
        ProofTreeFilter mf = new FilterHideClosed();
        filtersMap.put(mf, false);
    }

    /**
     * @return the filtersMap
     */
    public Map<ProofTreeFilter, Boolean> getFiltersMap() {
        return filtersMap;
    }

    public boolean getFilterStatus(ProofTreeFilter f) {
        return filtersMap.get(f);
    }
    
    public void toggleFilteringStatus(ProofTreeFilter f) {
        boolean act = !filtersMap.get(f);
        filtersMap.put(f, act);
        
        if (act) {
            root.filter(f);
        }
        else {
            root.filter(new FilterShowAll());
        }
    }
    
    //TODO
    public void setTree(ProofTreeItem r) {
        root = r;
    }
    
}
