/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model.impl;

import de.uka.ilkd.key.symbolic_execution.object_model.IModelSettings;

/**
 * Default implementation of {@link IModelSettings}.
 *
 * @author Martin Hentschel
 */
public class ModelSettings implements IModelSettings {
    /**
     * {@code true} use unicode characters, {@code false} do not use unicode characters.
     */
    private final boolean useUnicode;

    /**
     * {@code true} use pretty printing, {@code false} do not use pretty printing.
     */
    private final boolean usePrettyPrinting;

    /**
     * {@code true} simplify conditions, {@code false} do not simplify conditions.
     */
    private final boolean simplifyConditions;

    /**
     * Constructor.
     *
     * @param useUnicode {@code true} use unicode characters, {@code false} do not use unicode
     *        characters.
     * @param usePrettyPrinting {@code true} use pretty printing, {@code false} do not use pretty
     *        printing.
     * @param simplifyConditions {@code true} simplify conditions, {@code false} do not simplify
     *        conditions.
     */
    public ModelSettings(boolean useUnicode, boolean usePrettyPrinting,
            boolean simplifyConditions) {
        this.useUnicode = useUnicode;
        this.usePrettyPrinting = usePrettyPrinting;
        this.simplifyConditions = simplifyConditions;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isUseUnicode() {
        return useUnicode;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isUsePrettyPrinting() {
        return usePrettyPrinting;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isSimplifyConditions() {
        return simplifyConditions;
    }
}
