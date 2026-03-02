/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

import com.github.javaparser.Position;
import com.github.javaparser.Range;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.CallableDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.nodeTypes.NodeWithSimpleName;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.utils.PositionUtils;
import org.jspecify.annotations.NonNull;

public class JMLCommentTransformer extends JavaTransformer {
    public static final DataKey<List<Comment>> BEFORE_COMMENTS = new DataKey<>() {
    };
    public static final DataKey<List<Comment>> AFTER_COMMENTS = new DataKey<>() {
    };

    /**
     * creates a transformer for the recoder model
     *
     * @param services the CrossReferenceServiceConfiguration to access
     *        model information
     */
    public JMLCommentTransformer(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    private void attachComments(Node node, List<Comment> allComments) {
        if (!hasJmlCommentInside(node)) {
            return;
        }

        var orphan = node.getOrphanComments();
        for (Comment comment : orphan) {
            comment.setParentNode(node);
        }
        var filterComments = filterToplevel(allComments, node);
        filterComments.addAll(orphan);
        PositionUtils.sortByBeginPosition(filterComments);
        if (filterComments.isEmpty()) {
            return;
        }

        // attach to next Node
        Iterator<Node> iter = node.getChildNodes().iterator();
        int commentIdx = 0;

        Node n = null;
        nextNode: while (iter.hasNext() && commentIdx < filterComments.size()) {
            n = iter.next();
            List<Comment> specs = new ArrayList<>();
            while (commentIdx < filterComments.size()) {
                Comment c = filterComments.get(commentIdx);
                if (PositionUtils.areInOrder(n, c)) {
                    continue nextNode;
                }
                n.setData(BEFORE_COMMENTS, specs);
                specs.add(c);
                allComments.remove(c);
                commentIdx++;
            }
        }

        if (!allComments.isEmpty()) {
            var mods = allComments.stream().filter(it -> isModifier(node, it)).toList();
            if (!mods.isEmpty()) {
                allComments.removeAll(mods);
                List<Comment> specs = new ArrayList<>();
                try {
                    specs = node.getData(BEFORE_COMMENTS);
                } catch (Exception e) {
                }
                specs.addAll(mods);
                node.setData(BEFORE_COMMENTS, specs);
            }
        }

        if (commentIdx < filterComments.size()) {
            if (n != null) {
                List<Comment> specs = new ArrayList<>();
                n.setData(AFTER_COMMENTS, specs);
                var comments = filterComments.subList(commentIdx, filterComments.size());
                specs.addAll(comments);
                allComments.removeAll(comments);
            }
        }
    }

    private boolean isModifier(Node n, Comment c) {
        if (c.getRange().isEmpty() || n.getRange().isEmpty()) {
            return false;
        }

        Node end = null;
        if (n instanceof CallableDeclaration<?> || n instanceof TypeDeclaration) {
            end = ((NodeWithSimpleName<?>) n).getName();
        }

        if (end != null) {
            Position start = n.getRange().get().begin;
            Position stop = end.getRange().get().end;
            var b = within(start, stop, c.getRange().get());
            return b;
        }

        return false;
    }

    private boolean within(Position start, Position stop, Range range) {
        return start.compareTo(range.begin) <= 0 &&
                range.begin.compareTo(stop) <= 0;
    }

    private boolean hasJmlCommentInside(Node n) {
        return switch (n) {
            case CompilationUnit ignored -> true;
            case TypeDeclaration<?> ignored -> true;
            case BodyDeclaration<?> ignored -> true;
            case BlockStmt ignored -> true;
            case LabeledStmt ignored -> true;
            case WhileStmt ignored -> true;
            case ForStmt ignored -> true;
            case ForEachStmt ignored -> true;
            case DoStmt ignored -> true;
            case Type ignored -> true;
            case Parameter ignored -> true;
            case null, default -> false;
        };
    }

    private List<Comment> filterToplevel(List<Comment> comments, Node n) {
        var seq = comments.stream()
                .filter(it -> PositionUtils.nodeContains(n, it, false)) // inside n
                .filter(it -> n.getChildNodes().stream()
                        .noneMatch(child -> PositionUtils.nodeContains(child, it, true)))
                .collect(Collectors.toList());
        return seq;
    }

    @Override
    public void apply(CompilationUnit cu) {
        var comments = cu.getAllComments();
        cu.walk(it -> attachComments(it, comments));
        if (!comments.isEmpty()) {
            throw new IllegalStateException(
                "Some comments were not attached to nodes:\n\t" + comments);
        }
    }
}
