/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.util.Enumeration;
import java.util.List;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

public abstract class Streams {
    public static String toString(InputStream is) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        is.transferTo(out);
        return out.toString();
    }

    /// Translates the enumeration into stream.
    public static <T> Stream<T> fromEnumerator(Enumeration<T> enumeration) {
        return StreamSupport.stream(
            Spliterators.spliteratorUnknownSize(enumeration.asIterator(), Spliterator.ORDERED),
            false);
    }

    /// Returns a list given the elements in the enumeration.
    public static <T> List<T> toList(Enumeration<T> enumeration) {
        return fromEnumerator(enumeration).toList();
    }
}
