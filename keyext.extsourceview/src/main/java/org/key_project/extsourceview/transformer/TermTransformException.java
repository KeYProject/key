package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.JTerm;

/**
 * Transformation failed due to unusable input data
 * In contrast to InternTransformException this exception can happen in the normal program flow
 * For example if the input sequent still contains updates (is not fully simplified)
 */
public class TermTransformException extends TransformException {
    public final JTerm term;
    public TermTransformException(JTerm t, String message) {
        super(message);
        term = t;
    }
}
