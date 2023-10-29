package org.keyproject.key.api.remoteapi;

import de.uka.ilkd.key.gui.Example;

/**
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record ExampleDesc(String name, String description) {
    public static ExampleDesc from(Example example) {
        return new ExampleDesc(example.getName(), example.getDescription());
    }
}
