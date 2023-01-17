// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public class IllegalOptionValueException extends OptionException {

    String val;

    public IllegalOptionValueException(String opt, String val) {
        super(opt);
        this.val = val;
    }

    public String toString() {
        return "Illegal value \"" + val + "\" for option \"" + opt + "\"";
    }

}