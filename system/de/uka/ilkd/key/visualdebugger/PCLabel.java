package de.uka.ilkd.key.visualdebugger;

public class PCLabel implements Label {
    private int id;

    private boolean looking = false;

    public PCLabel(int i, boolean looking) {
        this.looking = looking;
        id = i;
    }

    public int getId() {
        return id;
    }

    public boolean isLooking() {
        return looking;
    }

    public void setLooking(boolean looking) {
        this.looking = looking;
    }

    public String toString() {
        return "PC(" + id + "," + looking + ")";
    }

}
