/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

/**
 * Problem report indicating that the planned transformation is not possible due to missing sources.
 * Subclasses of this class may provide detailed information about the missing parts.
 */
public abstract class MissingSources extends Problem {
    // nothing here
}
