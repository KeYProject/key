/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
