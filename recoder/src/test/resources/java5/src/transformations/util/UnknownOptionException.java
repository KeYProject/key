
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