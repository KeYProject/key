package recoder.java.statement;

public abstract class SwitchBranch extends Branch {

    public SwitchBranch() {
        super();
    }

    /**
     * Branch.
     *
     * @param proto a branch.
     */

    protected SwitchBranch(SwitchBranch proto) {
        super(proto);
    }

    @Override
    public Switch getParent() {
        return (Switch) parent;
    }

    /**
     * Set parent.
     *
     * @param parent a switch.
     */

    public void setParent(Switch parent) {
        this.parent = parent;
    }
}
