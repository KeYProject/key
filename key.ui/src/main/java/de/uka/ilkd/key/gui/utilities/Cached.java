/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.utilities;

import java.util.Objects;
import java.util.function.Function;

/**
 * Caches a computation using a single value cache
 *
 * @param <A> arguments for the computation
 * @param <T> return type
 */
public class Cached<A, T> {
    private A args = null;
    private T value = null;
    private final Function<A, T> update;

    /**
     * Constructor
     *
     * @param update the computation
     */
    public Cached(Function<A, T> update) {
        this.update = update;
    }

    /**
     * Gets a possibly cached value
     *
     * @param args the arguments
     * @return the value
     */
    public T get(A args) {
        if (Objects.equals(args, this.args)) {
            return value;
        }
        value = update.apply(args);
        this.args = args;
        return value;
    }
}
