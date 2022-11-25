package org.key_project.extsourceview.transformer;

public interface InsPositionProvider {
    class InsertionPosition {
        public final int Line;
        public final int Indentation;

        public InsertionPosition(int line, int indent) {
            Line = line;
            Indentation = indent;
        }
    }

    InsertionPosition getPosition(InsertionTerm term) throws TransformException, InternTransformException;
}
