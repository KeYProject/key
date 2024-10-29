package org.key_project.rusty.parser.hir;

import java.util.Arrays;

public record Path<R>(Span span, R res, PathSegment[] segments) {
    @Override
    public String toString() {
        return "Path{" +
                "span=" + span +
                ", res=" + res +
                ", segments=" + Arrays.toString(segments) +
                '}';
    }
}
