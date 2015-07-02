package de.uka.ilkd.key.util;

/**
 * Default implementation which wraps a boolean state field.
 *
 * @author ulbrich
 */
public class DefaultExperimentalFeature implements ExperimentalFeature {

    private boolean active;

    @Override
    public void deactivate() {
        this.active = false;
    }

    @Override
    public void activate() {
        this.active = true;
    }

    @Override
    public boolean active() {
        return active;
    }

}
