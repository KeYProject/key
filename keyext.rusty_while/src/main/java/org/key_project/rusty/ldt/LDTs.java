package org.key_project.rusty.ldt;

import org.key_project.rusty.Services;

public class LDTs {
    private final BoolLDT boolLDT;

    public LDTs(Services services) {
        boolLDT = new BoolLDT(services);
    }

    public BoolLDT getBoolLDT() {
        return boolLDT;
    }
}
