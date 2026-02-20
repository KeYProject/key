/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.stmt.*;
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
     * @param services
     *        the CrossReferenceServiceConfiguration to access
     *        model information
     */
    public JMLCommentTransformer(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    private void attachComments(Node cu, List<Comment> allComments) {
        if (!hasJmlCommentInside(cu)) {
            return;
        }

        var orphan = cu.getOrphanComments();
        for (Comment comment : orphan) {
            comment.setParentNode(cu);
        }
        var filterComments = filterToplevel(allComments, cu);
        filterComments.addAll(orphan);
        PositionUtils.sortByBeginPosition(filterComments);
        if (filterComments.isEmpty()) {
            return;
        }

        // attach to next Node
        Iterator<Node> iter = cu.getChildNodes().iterator();
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

    private boolean hasJmlCommentInside(Node cu) {
        if (cu instanceof CompilationUnit)
            return true;
        if (cu instanceof TypeDeclaration<?>)
            return true;
        if (cu instanceof BodyDeclaration<?>)
            return true;
        if (cu instanceof BlockStmt)
            return true;
        if (cu instanceof LabeledStmt) {
            return true;
        }
        if (cu instanceof WhileStmt) {
            return true;
        }
        if (cu instanceof ForStmt) {
            return true;
        }
        if (cu instanceof ForEachStmt) {
            return true;
        }
        if (cu instanceof DoStmt) {
            return true;
        }
        if (cu instanceof MethodDeclaration)
            return true;
        return false;
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
            throw new IllegalStateException("Some comments were not attached to nodes");
        }
    }
}
