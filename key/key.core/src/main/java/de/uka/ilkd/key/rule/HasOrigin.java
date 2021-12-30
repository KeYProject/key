package de.uka.ilkd.key.rule;

import javax.annotation.Nullable;

/**
 * @author Alexander Weigl
 * @version 1 (12/30/21)
 */
public interface HasOrigin {
    /**
     * Information about the origin of the rule.
     *
     * Should be a human-readable location where the user can find the declaration of the rule.
     *
     * This field is set by the parser with [url]:[lineNumber]
     */
    @Nullable
    default String getOrigin() { return null; }
}
