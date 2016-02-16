package de.uka.ilkd.key.nui.controller;

import de.uka.ilkd.key.nui.NUI;

public abstract class NUIController {

    protected NUI nui = null;
    protected String componentName = null;
    protected String filename = null;

    public void constructor(NUI nuiRef, String componentName, String filename) {
        this.nui = nuiRef;
        this.componentName = componentName;
        this.filename = filename;
        
        init();
    }
    
    protected abstract void init();

}
