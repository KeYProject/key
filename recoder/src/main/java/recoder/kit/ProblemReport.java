/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.kit;

/**
 * Problem report returned by the analysis phase of a {@link Transformation}. The problem report can
 * be used for interactions. This interface should not be subclassed directly, instead one of
 * {@link recoder.kit.NoProblem}or {@link recoder.kit.Problem}.
 *
 * @author AL
 * @see Transformation#execute
 * @see TwoPassTransformation#analyze
 */
public interface ProblemReport {
    // nothing here
}
