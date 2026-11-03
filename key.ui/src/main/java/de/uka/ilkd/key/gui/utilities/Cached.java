/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.utilities;

import java.util.Objects;
import java.util.function.Function;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Caches a computation using a single value cache
 *
 * @param <A> arguments for the computation
 * @param <T> return type
 */
@NullMarked
public class Cached<A extends @Nullable Object, T extends @Nullable Object> {
    private @Nullable A args = null;
    private @Nullable T value = null;
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
     * @return the value, or {@code null} if the cached computation produced {@code null}
     */
    public @Nullable T get(A args) {
        if (Objects.equals(args, this.args)) {
            return value;
        }
        value = update.apply(args);
        this.args = args;
        return value;
    }
}
