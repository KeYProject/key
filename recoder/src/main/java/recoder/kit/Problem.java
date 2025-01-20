/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

/**
 * Problem report returned by the analysis phase of a {@link Transformation} indicating that the
 * planned transformation is not applicable. This is dual to the
 * {@link recoder.kit.NoProblem}report. This class is also an exception but is usually not thrown,
 * but passed on as ordinary return value.
 *
 * @author AL
 * @see recoder.kit.NoProblem
 */
public abstract class Problem extends RuntimeException implements ProblemReport {
    // nothing here
}
