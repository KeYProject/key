package org.key_project.ui.interactionlog.api;

/**
 * @author Alexander Weigl
 * @version 1 (08.05.19)
 */
public interface Markdownable {
    default String getMarkdown() {
        return String.format("**Unsupported interaction: %s**%n%n", this.getClass().getName());
    }
}
