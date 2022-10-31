package org.key_project.extsourceview.transformer;

import de.uka.ilkd.key.java.PositionInfo;

public class PositionMap {

    private final PositionInfo methodPosition;

    public PositionMap(PositionInfo mpos) {
        this.methodPosition = mpos;
    }

    public int getLineForInsTerm(InsertionTerm iterm) throws InternTransformException {
        if (iterm.Type == InsertionType.ENSURES) {
            return methodPosition.getStartPosition().getLine();
        }
        if (iterm.Type == InsertionType.REQUIRES) {
            return methodPosition.getStartPosition().getLine() + 1;
        }
        throw new InternTransformException("unknown InsertionTerm.Type");
    }

    public int getLineIndent(int line) {
        return 9; //TODO
    }
}
