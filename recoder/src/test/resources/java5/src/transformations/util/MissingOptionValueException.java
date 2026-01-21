// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public class MissingOptionValueException extends OptionException {

    public MissingOptionValueException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing value for option \"" + opt + "\"";
    }

}