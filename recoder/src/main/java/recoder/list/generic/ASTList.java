/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.list.generic;

import recoder.java.SourceElement;

import java.util.List;

public interface ASTList<E extends SourceElement> extends List<E> {
    ASTList<E> deepClone();

    void trimToSize();
}
