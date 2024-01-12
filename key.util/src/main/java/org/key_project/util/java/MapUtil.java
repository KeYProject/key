/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collector;
import java.util.stream.Collector.Characteristics;
import java.util.stream.Collectors;

/**
 * Utility methods for maps.
 *
 * @author lanzinger
 */
public final class MapUtil {

    private MapUtil() {}

    /**
     * <p>
     * Custom collector for maps.
     * </p>
     *
     * <p>
     * This collector behaves like {@link Collectors#toMap(Function, Function)} except that it
     * allows {@code null} values.
     * </p>
     *
     * @param keyMapper map function for the key set.
     * @param valueMapper map function for the value set.
     * @return a collector for maps.
     */
    public static <E, K, V> Collector<E, Map<K, V>, Map<K, V>> collector(
            Function<? super E, ? extends K> keyMapper,
            Function<? super E, ? extends V> valueMapper) {
        return Collector.of(HashMap::new,
            (map, entry) -> map.put(keyMapper.apply(entry), valueMapper.apply(entry)),
            (map1, map2) -> {
                map1.putAll(map2);
                return map1;
            }, Characteristics.UNORDERED);
    }
}
