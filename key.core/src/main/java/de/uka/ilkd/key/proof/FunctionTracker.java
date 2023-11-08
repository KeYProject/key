/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof;

import java.lang.ref.WeakReference;
import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.op.Function;

public final class FunctionTracker {
    private static final WeakHashMap<Function, WeakReference<Node>> mapping = new WeakHashMap<>();

    private FunctionTracker() {

    }

    public static void setIntroducedBy(Function f, Node n) {
        mapping.put(f, new WeakReference<>(n));
    }

    public static Node getIntroducedBy(Function f) {
        var x = mapping.get(f);
        return x != null ? x.get() : null;
    }
}
