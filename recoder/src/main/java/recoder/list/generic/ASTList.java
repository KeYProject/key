/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.list.generic;

import java.util.List;

import recoder.java.SourceElement;

public interface ASTList<E extends SourceElement> extends List<E> {
    ASTList<E> deepClone();

    void trimToSize();
}
