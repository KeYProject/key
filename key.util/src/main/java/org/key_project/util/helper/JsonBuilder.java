/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.helper;

import java.util.Collection;

public interface JsonBuilder {
    JsonBuilder newObject(String key);

    JsonBuilder newObject(int index);

    JsonBuilder newArray(String key);

    void putString(String key, String value);

    void putString(int index, String value);

    /**
     * Set all array elements based on the provided list.
     *
     * @param values values to set
     */
    void setFrom(Collection<String> values);
}
