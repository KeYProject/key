package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.DataKey;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.BodyDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.comments.Comment;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.utils.PositionUtils;

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
    public JMLCommentTransformer(@Nonnull TransformationPipelineServices services) {
        super(services);
    }

    private void attachComments(Node cu, List<Comment> allComments) {
        if (!hasJmlCommentInside(cu)) {
            return;
        }

        var filterComments = filterToplevel(allComments, cu);
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
                // TODO javaparser this is useless, the list is an accumulation returned by
                // javaparser
                allComments.remove(c);
                commentIdx++;
            }
        }

        if (commentIdx < filterComments.size()) {
            if (n != null) {
                List<Comment> specs = new ArrayList<>();
                n.setData(AFTER_COMMENTS, specs);
                specs.addAll(filterComments.subList(commentIdx, filterComments.size() - 1));
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
        return false;
    }

    private List<Comment> filterToplevel(List<Comment> comments, Node n) {
        var seq = comments.stream()
                .filter(it -> PositionUtils.nodeContains(n, it, false)) // inside n
                .filter(it -> n.getChildNodes().stream()
                        .noneMatch(child -> PositionUtils.nodeContains(child, it, true)))
                .collect(Collectors.toList());
        PositionUtils.sortByBeginPosition(seq);
        return seq;
    }

    @Override
    public void apply(CompilationUnit cu) {
        var comments = cu.getAllComments();
        cu.walk(it -> attachComments(it, comments));
    }
}
