// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public class UnknownOptionException extends OptionException {

    public UnknownOptionException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Unknown option \"" + opt + "\"";
    }

}