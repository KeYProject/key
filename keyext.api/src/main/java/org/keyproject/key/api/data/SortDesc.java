/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.keyproject.key.api.data;

import java.util.List;

import org.key_project.logic.sort.Sort;

/**
 * @author Alexander Weigl
 * @version 1 (13.10.23)
 */
public record SortDesc(String string, String documentation,
                       List<SortDesc> extendsSorts,
                       boolean anAbstract, String s) implements KeYDataTransferObject {
    public static SortDesc from(Sort sort) {
        return new SortDesc(sort.name().toString(), sort.getDocumentation(),
                sort.extendsSorts().stream().map(SortDesc::from).toList(),
                sort.isAbstract(), sort.declarationString());
    }
}
