/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

/**
 * Problem report returned by the analysis phase of a {@link Transformation} indicating that the
 * planned transformation is applicable. This does not guarantee that the functional behavior will
 * be retained.
 * <p>
 * Instead of creating a new object, the {@link recoder.kit.Transformation#NO_PROBLEM}constant
 * should be used.
 *
 * @author AL
 * @see recoder.kit.Equivalence
 */
public class NoProblem implements ProblemReport {

    /**
     * Externally invisible constructor.
     */
    NoProblem() {
        super();
    }
}
