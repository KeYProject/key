// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public class MissingOptionValueException extends OptionException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2394702516972821831L;

    public MissingOptionValueException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing value for option \"" + opt + "\"";
    }

}
