package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.logic.Term;

public class TermTransformException extends TransformException {
    public final Term Term;
    public TermTransformException(Term t, String message) {
        super(message);
        Term = t;
    }
}
