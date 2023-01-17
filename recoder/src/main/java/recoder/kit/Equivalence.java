// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

/**
 * Problem report indicating that the planned transformation is applicable and will not change the
 * functional behavior of the program.
 * <p>
 * Instead of creating a new object, the {@link recoder.kit.Transformation#EQUIVALENCE}constant
 * should be used.
 *
 * @author AL
 */
public class Equivalence extends NoProblem {
    Equivalence() {
        super();
    }
}
