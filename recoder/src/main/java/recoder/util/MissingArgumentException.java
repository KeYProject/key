// This file is part of the RECODER library and protected by the LGPL

package recoder.util;

/**
 * @author RN
 */
public class MissingArgumentException extends OptionException {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -202835350467537194L;

    public MissingArgumentException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing mandatory argument \"" + opt + "\"";
    }

}
