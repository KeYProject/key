
package recoder.abstraction;

import java.util.List;

/**
 * A program model element representing fields.
 *
 * @author AL
 * @author RN
 * @author TG
 */
public interface Field extends Variable, Member {
    List<? extends TypeArgument> getTypeArguments();
}