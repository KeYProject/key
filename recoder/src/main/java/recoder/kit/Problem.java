// This file is part of the RECODER library and protected by the LGPL.

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
