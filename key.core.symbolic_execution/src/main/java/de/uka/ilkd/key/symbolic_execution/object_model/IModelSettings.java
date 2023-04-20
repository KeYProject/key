package de.uka.ilkd.key.symbolic_execution.object_model;

/**
 * Provides the settings used to construct a symbolic object model.
 *
 * @author Martin Hentschel
 */
public interface IModelSettings {
    /**
     * Checks if unicode characters are used.
     *
     * @return {@code true} use unicode characters, {@code false} do not use unicode characters.
     */
    boolean isUseUnicode();

    /**
     * Checks if pretty printing is used or not.
     *
     * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
     */
    boolean isUsePrettyPrinting();

    /**
     * Checks if conditions should be simplified or not.
     *
     * @return {@code true} simplify conditions, {@code false} do not simplify conditions.
     */
    boolean isSimplifyConditions();
}
