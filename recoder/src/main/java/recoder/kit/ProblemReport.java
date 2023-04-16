// This file is part of the RECODER library and protected by the LGPL.
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
