/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
