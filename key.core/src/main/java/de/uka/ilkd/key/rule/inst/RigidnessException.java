package de.uka.ilkd.key.rule.inst;

/**
 * this exception is thrown if non-rigid instantiation has been given for a schema variable only
 * allowing rigid instantiations
 */
public class RigidnessException extends IllegalInstantiationException {

    /**
     *
     */
    private static final long serialVersionUID = 1109354128591892703L;

    public RigidnessException(String description) {
        super(description);
    }


}
