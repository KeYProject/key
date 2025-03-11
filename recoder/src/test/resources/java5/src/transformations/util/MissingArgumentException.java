
package recoder.util;

/**
 * @author RN
 */
public class MissingArgumentException extends OptionException {

    public MissingArgumentException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Missing mandatory argument \"" + opt + "\"";
    }

}