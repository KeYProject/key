/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import de.uka.ilkd.key.gui.Example;

/**
 * This class represents a built-in example.
 * TODO (weigl,rpc) Also deliver the contents of the example (files)?
 *
 * @param name the name of the example, also used as an identifer
 * @param description a description of the example
 * @author Alexander Weigl
 * @version 1 (29.10.23)
 */
public record ExampleDesc(String name, String description) {
    public static ExampleDesc from(Example example) {
        return new ExampleDesc(example.getName(), example.getDescription());
    }
}
