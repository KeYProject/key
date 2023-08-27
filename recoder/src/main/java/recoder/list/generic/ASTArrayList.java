/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.list.generic;

import java.util.ArrayList;
import java.util.Collection;

import recoder.java.SourceElement;

public class ASTArrayList<E extends SourceElement> extends ArrayList<E> implements ASTList<E> {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 3179494289054893052L;

    public ASTArrayList() {
        super();
    }

    public ASTArrayList(Collection<E> c) {
        super(c);
    }

    public ASTArrayList(int initialCapacity) {
        super(initialCapacity);
    }

    public ASTArrayList(E initialItem) {
        this(1);
        add(initialItem);
    }

    public ASTArrayList<E> deepClone() {
        ASTArrayList<E> result = new ASTArrayList<>(size());
        for (E e : this) {
            @SuppressWarnings("unchecked")
            E deepClone = (E) e.deepClone();
            result.add(deepClone);
        }
        return result;
    }

}
