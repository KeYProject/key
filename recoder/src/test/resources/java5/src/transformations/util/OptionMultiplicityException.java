
package recoder.util;

/**
 * @author RN
 */
public class OptionMultiplicityException extends OptionException {

    public OptionMultiplicityException(String opt) {
        super(opt);
    }

    public String toString() {
        return "Option \"" + opt + "\" does not allow multiple values";
    }

}