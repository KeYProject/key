package org.key_project.jmlediting.core.resolver;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.IBinding;

public class ResolveResult {
    
    private boolean isFinalized = false;
    private String name = "";
    private ResolveResultType type = ResolveResultType.UNSPECIFIED;
    private List<Integer> indexOffsets = new ArrayList<Integer>();
    private IBinding binding = null;    // Should I save this? :( Comment says it takes a LOT of resources.
    
    public ResolveResult(String name, ResolveResultType type, IBinding binding) {
        this.name = name;
        this.type = type;
        this.binding = binding;
    }
    
    public List<Integer> getIndexOffsets() {
        return indexOffsets;
    }
    
    public boolean addOffset(int offset) {
        if(isFinalized) return false;
        
        indexOffsets.add(offset);
        return true;
    }

    public IBinding getBinding() {
        return binding;
    }

    public String getName() {
        return name;
    }

    public ResolveResultType getType() {
        return type;
    }
    
    public void finalize() {
        isFinalized = true;
    }
}
