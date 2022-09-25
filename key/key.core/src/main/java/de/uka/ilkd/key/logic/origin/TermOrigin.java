package de.uka.ilkd.key.logic.origin;

import de.uka.ilkd.key.logic.label.OriginTermLabel;
import org.key_project.util.collection.ImmutableList;

import java.net.URI;
import java.util.ArrayList;

public class TermOrigin {

    public static final ImmutableList<TermOrigin> EMPTY = ImmutableList.fromList(new ArrayList<>());

    public final String File;

    public final int LineStart;
    public final int LineEnd;

    public final int PositionStart;
    public final int PositionEnd;

    public final OriginTermLabel.SpecType Type;

    public TermOrigin(String file, int lineStart, int lineEnd, int positionStart, int positionEnd, OriginTermLabel.SpecType type) {
        File = file;
        LineStart = lineStart;
        LineEnd = lineEnd;
        PositionStart = positionStart;
        PositionEnd = positionEnd;
        Type = type;
    }
}
