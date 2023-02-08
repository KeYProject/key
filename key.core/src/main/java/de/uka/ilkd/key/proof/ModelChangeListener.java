package de.uka.ilkd.key.proof;

/**
 * this interface is implemented by listener of change events of a model
 */

public interface ModelChangeListener {

    /** this method is called if the model has changed */
    void modelChanged(ModelEvent me);

}
