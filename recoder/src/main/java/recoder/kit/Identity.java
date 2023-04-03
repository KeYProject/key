// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

/**
 * Problem report indicating that the planned transformation is redundant. The syntactic
 * transformation itself can be skipped.
 * <p>
 * Instead of creating a new object, the {@link recoder.kit.Transformation#IDENTITY}constant should
 * be used.
 *
 * @author AL
 */
public class Identity extends Equivalence {
    Identity() {
        super();
    }
}
