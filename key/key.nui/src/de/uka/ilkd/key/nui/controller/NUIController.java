package de.uka.ilkd.key.nui.controller;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.NUI;

public abstract class NUIController {

    protected NUI nui = null;
    protected String componentName = null;
    protected String filename = null;
    protected DataModel dataModel = null;

    public void constructor(NUI nuiRef, DataModel dataModel,
            String componentName, String filename) {
        this.nui = nuiRef;
        this.dataModel = dataModel;
        this.componentName = componentName;
        this.filename = filename;

        init();
    }

    protected abstract void init();

}
