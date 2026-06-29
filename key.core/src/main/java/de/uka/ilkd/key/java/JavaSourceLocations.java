/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java;

import java.net.URI;
import java.util.Optional;

import de.uka.ilkd.key.java.ast.PositionInfo;

import org.key_project.util.parsing.Location;
import org.key_project.util.parsing.Position;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import org.jspecify.annotations.Nullable;

/**
 * JavaParser-aware factories for {@link Position} and {@link Location}.
 * <p>
 * {@code Position}/{@code Location} themselves live in {@code key.ncore} and must stay free of any
 * JavaParser (and other target-language) dependencies. The conversions from JavaParser positions
 * and AST nodes therefore live here, in {@code key.core}.
 */
public final class JavaSourceLocations {

    private JavaSourceLocations() {}

    /**
     * Converts a JavaParser position into a KeY {@link Position}.
     *
     * @param p a JavaParser position, may be {@code null}
     * @return the corresponding KeY position, or {@link Position#UNDEFINED} if {@code p} is missing
     *         or invalid
     */
    public static Position positionFromJP(com.github.javaparser.@Nullable Position p) {
        if (p == null || p.invalid() || (p.line == -1 && p.column == -1)) {
            return Position.UNDEFINED;
        } else {
            return Position.newOneBased(p.line, p.column);
        }
    }

    /**
     * Builds a {@link Location} from a JavaParser AST node (using its compilation unit's storage
     * path and the node's begin position).
     *
     * @param n a JavaParser node
     * @return the corresponding location
     */
    public static Location locationFromNode(Node n) {
        var fileUri = n.findCompilationUnit().flatMap(CompilationUnit::getStorage)
                .map(it -> it.getPath().toUri())
                .orElse(null);

        var pos = n.getRange().map(it -> it.begin).orElse(null);
        return new Location(fileUri, positionFromJP(pos));
    }

    /**
     * Builds a {@link Location} from a {@link PositionInfo} (a KeY source-element position carrying
     * a file URI and a start position).
     *
     * @param info the position info
     * @return the corresponding location, or {@link Location#UNDEFINED} if no file URI is available
     */
    public static Location fromPositionInfo(PositionInfo info) {
        Optional<URI> uri = info.getURI();
        if (uri.isEmpty()) {
            return Location.UNDEFINED;
        } else {
            Position pos = info.getStartPosition();
            return new Location(uri.get(), pos);
        }
    }
}
