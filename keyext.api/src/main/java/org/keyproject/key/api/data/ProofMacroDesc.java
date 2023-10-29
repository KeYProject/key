package org.keyproject.key.api.data;

import de.uka.ilkd.key.macros.ProofMacro;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record ProofMacroDesc(String name, String category, String description, String scriptCommandName) {
    public static ProofMacroDesc from(ProofMacro proofMacro) {
        return new ProofMacroDesc(proofMacro.getName(), proofMacro.getCategory(),
                proofMacro.getDescription(), proofMacro.getScriptCommandName());
    }
}
