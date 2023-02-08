/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL.

package recoder.kit;

/**
 * Problem report indicating that the planned transformation is applicable and will not change the
 * functional behavior of the program.
 * <p>
 * Instead of creating a new object, the {@link recoder.kit.Transformation#EQUIVALENCE}constant
 * should be used.
 *
 * @author AL
 */
public class Equivalence extends NoProblem {
    Equivalence() {
        super();
    }
}
