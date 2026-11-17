/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.util;

@FunctionalInterface
public interface QuadFunction<T1, T2, T3, T4, T> {
    T apply(T1 t1, T2 t2, T3 t3, T4 t4);
}
