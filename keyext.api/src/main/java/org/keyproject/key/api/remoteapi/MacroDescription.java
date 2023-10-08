package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.macros.ProofMacro;

public record MacroDescription(String name, String description, String category) {
    public static MacroDescription from(ProofMacro m) {
        return new MacroDescription(m.getName(), m.getDescription(), m.getCategory());
    }
}
