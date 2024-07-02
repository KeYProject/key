package org.key_project.ui.interactionlog.api;

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
public interface Scriptable {
    default String getProofScriptRepresentation() {
        return "// Unsupported interaction: " + getClass() + "\n";
    }
}
