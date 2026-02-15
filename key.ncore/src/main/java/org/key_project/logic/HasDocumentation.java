package org.key_project.logic;

import org.jspecify.annotations.Nullable;

public interface HasDocumentation {
    String getDocumentationKey();
    
    default @Nullable String getDocumentation() {
        return null;
    }

    record OptionCategory(String name) implements HasDocumentation {
        public String getDocumentationKey() {
            return "category/" + name;
        }
    }
}
