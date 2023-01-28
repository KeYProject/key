// This file is part of the RECODER library and protected by the LGPL.

package recoder.java.declaration.modifier;

/**
 * Visibility modifier.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class VisibilityModifier extends recoder.java.declaration.Modifier {

    /**
     * Visibility modifier.
     */

    public VisibilityModifier() {
        // default constructor
    }

    /**
     * Visibility modifier.
     *
     * @param proto a visibility modifier.
     */

    protected VisibilityModifier(VisibilityModifier proto) {
        super(proto);
    }
}
