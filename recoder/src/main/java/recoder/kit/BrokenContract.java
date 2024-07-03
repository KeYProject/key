/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of the RECODER library and protected by the LGPL

package recoder.kit;

/**
 * Problem report indicating that the planned transformation breaks a contract
 * even though there is no typing conflict. Usually this may happen in the
 * context of polymorph methods. This class of problems is usually a
 * conservative estimation only. Subclasses of this class may provide detailed
 * information about the reasons.
 */
public abstract class BrokenContract extends Problem {
    // nothing here
}
