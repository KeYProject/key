/*
 * Copyright (c) 2005, 2016, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package org.key_project.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.*;
import java.util.stream.Stream;

public final class ServiceLoaderUtil {
    private static final String PREFIX = "META-INF/services/";

    /**
     * Backport of {@link ServiceLoader#stream()} for Java8.
     * weigl: Should be replaced by if we upgrade.
     */
    @Deprecated
    public static <S> Stream<Class<S>> stream(Class<S> c) {
        ClassLoader cloader = c.getClassLoader();
        Set<String> classes = new HashSet<>();
        try {
            Enumeration<URL> iter = cloader.getResources(PREFIX + c.getName());
            while (iter.hasMoreElements()) {
                try (BufferedReader br = new BufferedReader(
                        new InputStreamReader(iter.nextElement().openStream()))) {
                    String line;
                    while ((line = br.readLine()) != null) {
                        line = line.trim();
                        if (line.isEmpty() || line.startsWith("#"))
                            continue;
                        classes.add(line);
                    }
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
            return classes.stream()
                    .map(it -> {
                        try {
                            return (Class<S>) Class.forName(it);
                        } catch (ClassNotFoundException e) {
                            e.printStackTrace();
                            return null;
                        }
                    })
                    .filter(Objects::nonNull);
        } catch (IOException e) {
            e.printStackTrace();
        }
        return Stream.empty();
    }
}