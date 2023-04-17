package de.uka.ilkd.key.logic;

/** BooleanContainer wraps primitive bool */
public final class BooleanContainer {
    private boolean bool;

    public BooleanContainer() {
        bool = false;
    }

    public boolean val() {
        return bool;
    }

    public void setVal(boolean b) {
        bool = b;
    }
}
