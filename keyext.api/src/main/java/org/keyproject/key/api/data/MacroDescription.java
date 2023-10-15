package org.keyproject.key.api.data;

import de.uka.ilkd.key.macros.ProofMacro;

/**
 *
 * @param name
 * @param description
 * @param category
 */
public record MacroDescription(String name, String description, String category) {
    public static MacroDescription from(ProofMacro m) {
        return new MacroDescription(m.getName(), m.getDescription(), m.getCategory());
    }
}
