/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
// This file is part of the RECODER library and protected by the LGPL

package recoder.kit;

/**
 * Problem report indicating that the planned transformation produces a conflict with existing model
 * elements. Subclasses of this class may provide detailed information about the reasons.
 */
public abstract class Conflict extends Problem {
    // nothing here
}

