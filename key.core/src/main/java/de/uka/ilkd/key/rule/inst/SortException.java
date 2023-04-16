package de.uka.ilkd.key.rule.inst;

/**
 * this exception is thrown from an "SVInstantiations"-Object if the sorts of a schema variable and
 * its instantiation are not compatible (and not generic)
 */
public class SortException extends IllegalInstantiationException {

    /**
     *
     */
    private static final long serialVersionUID = -1659749880755516351L;

    public SortException(String description) {
        super(description);
    }


}
