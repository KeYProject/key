/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package recoder.testsuite.basic.analysis;

import recoder.abstraction.ProgramModelElement;
import recoder.convenience.Format;
import recoder.java.Reference;

public abstract class XReferenceCompletenessTest {
    protected static String makeResolutionError(Reference r, ProgramModelElement x,
            ProgramModelElement y) {
        return Format.toString("%c %N @%p in %f", r) + " was found in reference list "
                + Format.toString("%c %N", x) + " but is resolved to " + Format.toString("%N", y);
    }
}
