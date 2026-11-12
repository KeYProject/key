/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.plugins.javac;

import java.util.List;

import de.uka.ilkd.key.proof.Proof;

/**
 * Stores diagnostics produced when compiling a Java source file, FX port of the Swing
 * {@code JavacData} (Swing {@code key.ui/plugins/javac/JavacExtension.java}, package-private
 * there — the FX port registers its own instance in the proof's user data, keyed by this class).
 *
 * @see JavacExtensionF
 */
class JavacData {

    /**
     * The diagnostics emitted by the compiler.
     */
    List<PositionedIssueStringF> issues = null;

    /**
     * True if there was no Java source file to compile.
     */
    boolean nonJavaProof;

    /**
     * Reads the extension's data of the given proof, throwing {@link IllegalStateException} when
     * the check has not run for it yet (the Swing code distinguishes the two states this way,
     * JavacExtension.java:129-136).
     *
     * @param proof the proof to read from
     * @return the stored data
     */
    static JavacData of(Proof proof) {
        return proof.getUserData().get(JavacData.class);
    }
}
