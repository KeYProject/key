package de.uka.ilkd.key.nui.prooftree.filter;

import de.uka.ilkd.key.nui.prooftree.NUINode;

@FilterAnnotation(isFilter = true)
public class TestFilter implements ProofTreeFilter {

    @Override
    public boolean test(NUINode t) {
        return false;
    }

    @Override
    public String getContextMenuItemText() {
        return "TestFilter";
    }

}
