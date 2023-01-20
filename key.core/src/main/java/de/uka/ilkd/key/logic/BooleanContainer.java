package de.uka.ilkd.key.logic;

/** BooleanContainer wraps primitive bool */
public final class BooleanContainer {
    private boolean bool;

    public BooleanContainer() {
        bool = false;
    }

    public final boolean val() {
        return bool;
    }

    public final void setVal(boolean b) {
        bool = b;
    }
}
