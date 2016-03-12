package de.uka.ilkd.key.nui.controller;

import java.util.ResourceBundle;

import de.uka.ilkd.key.nui.DataModel;
import de.uka.ilkd.key.nui.NUI;

public abstract class NUIController {

    protected NUI nui = null;
    protected String componentName = null;
    protected String filename = null;
    protected DataModel dataModel = null;
    protected ResourceBundle bundle = null;

    public void constructor(NUI nuiRef, DataModel dataModel,
            ResourceBundle bundle, String componentName, String filename) {
        this.nui = nuiRef;
        this.dataModel = dataModel;
        this.bundle = bundle;
        this.componentName = componentName;
        this.filename = filename;

        init();
    }

    protected abstract void init();

}
