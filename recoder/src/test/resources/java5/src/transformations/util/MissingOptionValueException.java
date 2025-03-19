
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