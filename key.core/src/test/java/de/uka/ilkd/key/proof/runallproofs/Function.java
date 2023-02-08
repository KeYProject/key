/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.proof.runallproofs;

/**
 * Function interface from Java 8. This interface can be removed once KeY moves from Java 7 to Java
 * 8.
 */
public interface Function<A, B> {
    public B apply(A a);
}
