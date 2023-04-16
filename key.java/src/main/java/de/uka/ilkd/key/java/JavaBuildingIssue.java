package de.uka.ilkd.key.java;


import com.github.javaparser.ast.Node;
import de.uka.ilkd.key.speclang.PositionedString;

import javax.annotation.Nullable;
import java.net.URI;

/**
 * @author Alexander Weigl
 * @version 1 (16.04.23)
 */
public class JavaBuildingIssue {
    private final Node node;
    private final String message;

    public JavaBuildingIssue(String message, Node node) {
        this.message = message;
        this.node = node;
    }

    public PositionedString getPositionedString() {
        return new PositionedString(message, getPath().toString(), getPosition());
    }

    public String getMessage() {
        return message;
    }

    public Position getPosition() {
        return Position.fromOneZeroBased(getLine(), getColumn());
    }

    @Nullable
    public URI getPath() {
        return node.findCompilationUnit()
                .flatMap(it -> it.getStorage()).map(it -> it.getPath().toUri()).orElse(null);
    }

    public int getLine() {
        return node.getRange().map(it -> it.begin).map(it -> it.line).orElse(-1);
    }

    public int getColumn() {
        return node.getRange().map(it -> it.begin).map(it -> it.column).orElse(-1);
    }
}
