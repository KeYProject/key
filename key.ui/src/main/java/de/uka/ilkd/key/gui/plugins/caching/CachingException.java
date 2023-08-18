/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.plugins.caching;

/**
 * Helpful error message used when the proof cache cannot
 * be applied successfully.
 *
 * @author Arne Keller
 */
public class CachingException extends Exception {
    private static final String EXPLANATION_TEXT =
        "Proof caching error: failed to realize cached branch\n\n" +
            "The replay system failed to reconstruct the referenced proof. Possible reasons:\n" +
            "1) the referenced proof has different \\include directives than the new proof\n" +
            "2) the referenced proof uses a different (bootstrap) classpath\n" +
            "3) an unknown error occurred\n\n" +
            "Try saving and reloading all currently opened proofs. Please also report this bug to the KeY team.";

    public CachingException(Exception e) {
        super(EXPLANATION_TEXT, e);
    }
}
